-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
-- name    : UniversalNonstochastic_Main_ElementaryModels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:57.980989+00:00
-- url     : https://prove2.me/theorems/d28b58b5-8208-4045-95a3-961cde6c1f83
-- title:
--   Elementary probability measures, deficiencies, $d_F$, $d_e$, $d^{\rm set}$ and $N_{\alpha,\beta}(d)$
-- statement:
--   An **elementary probability measure** $Q$ on $\mathbb N$ has finite support, rational atom masses $Q(\{\omega\})\ge0$ and total mass exactly $1$. It is a finite object, coded by the standard code of the list of triples (atom, numerator, denominator) over its support in increasing order. $K(Q)$ and $K(\omega\mid Q)$ are the prefix complexities of this code (unconditional, and as auxiliary input). For a nonempty finite set $\Omega$, $U_\Omega$ is the uniform measure, with mass $1/|\Omega|$ on each point of $\Omega$.
--
--   A **deficiency** is a function $d(\omega\mid Q)\in(-\infty,+\infty]$ of an object $\omega$ and an elementary probability measure $Q$ that is lower semicomputable uniformly in both arguments: the triples $(\omega,\text{code of }Q,r)$ with $r<d(\omega\mid Q)$ form a recursively enumerable set. For $\alpha\in\mathbb N_0$ and real $\beta$,
--   $$N_{\alpha,\beta}(d)=\{\omega : \text{there is no elementary }Q\text{ with }K(Q)\le\alpha\text{ and }d(\omega\mid Q)\le\beta\}.$$
--
--   For a function $F:\mathbb N\to\mathbb N_0$, with $-\log_2 0=+\infty$,
--   $$d_F(\omega\mid Q)=-\log_2 Q(\{\omega\})-F(\omega)\quad(12),\qquad d_e(\omega\mid Q)=-\log_2 Q(\{\omega\})-K(\omega\mid Q)\quad(11).$$
--   For a deficiency $d$, $d^{\rm set}(\omega\mid Q)=d(\omega\mid Q)$ if $Q=U_\Omega$ for a nonempty finite $\Omega$, and $+\infty$ otherwise.
--
--   These are the models and deficiencies of Sects. 3–4 of the source. Theorem 10 is stated for a general deficiency, and $d_F$ appears in its hypothesis (13).
--
--   **Formalization Note** Deficiencies take values in `EReal` and are never $-\infty$. $\log_2$ is `Real.logb 2`, applied only to positive masses: the zero-mass case is $+\infty$ by definition. Calibration conditions (p-tests, e-tests) are not part of the definition of a deficiency, as in the source.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. 3 pp.7–8 (elementary probability measures), Sect. 4 pp.10–11 (deficiency, N_{α,β}(d), equations (11), (12), d^set)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_Complexity

namespace UniversalNonstochastic.Main

/-- An elementary probability measure on `ℕ = {1, 2, …}`: finite support, rational atom
masses, total mass exactly `1`. `supp` is exactly the set of atoms of positive mass. -/
structure ElemMeasure where
  w : ℕ+ → ℚ
  supp : Finset ℕ+
  mem_supp : ∀ n, n ∈ supp ↔ 0 < w n
  nonneg : ∀ n, 0 ≤ w n
  total : ∑ n ∈ supp, w n = 1

/-- The code of an elementary probability measure: the standard code of the list of
triples (atom, numerator, denominator) over its support in increasing order. -/
def ElemMeasure.code (Q : ElemMeasure) : ℕ :=
  Encodable.encode ((Q.supp.sort (· ≤ ·)).map
    fun a : ℕ+ => ((a : ℕ), (Q.w a).num, (Q.w a).den))

/-- Prefix complexity of an elementary probability measure, `K(Q)`. -/
noncomputable def Kmeas (U : OptimalPrefixDecoder) (Q : ElemMeasure) : ℕ∞ :=
  U.K Q.code noCond

/-- Conditional prefix complexity of an object given an elementary measure, `K(ω | Q)`. -/
noncomputable def KobjGivenMeas (U : OptimalPrefixDecoder) (ω : ℕ+) (Q : ElemMeasure) : ℕ∞ :=
  U.K (objCode ω) Q.code

/-- The uniform probability measure `U_Ω` on a nonempty finite set `Ω`. -/
def uniform (Ω : Finset ℕ+) (hΩ : Ω.Nonempty) : ElemMeasure where
  w n := if n ∈ Ω then (1 : ℚ) / Ω.card else 0
  supp := Ω
  mem_supp n := by
    have hc : (0 : ℚ) < Ω.card := by exact_mod_cast hΩ.card_pos
    by_cases h : n ∈ Ω <;> simp [h, hc]
  nonneg n := by
    by_cases h : n ∈ Ω <;> simp [h]
  total := by
    have hc : (Ω.card : ℚ) ≠ 0 := by exact_mod_cast hΩ.card_pos.ne'
    rw [Finset.sum_ite_of_true (fun _ h => h), Finset.sum_const, nsmul_eq_mul]
    field_simp

/-- A deficiency: a function `d(ω | Q)` of an object and an elementary probability measure,
with values in `(-∞, +∞]`, lower semicomputable uniformly in both arguments (the set of
triples `(ω, code Q, r)` with `r < d(ω | Q)` is recursively enumerable). -/
def IsDeficiency (d : ℕ+ → ElemMeasure → EReal) : Prop :=
  (∀ ω Q, d ω Q ≠ ⊥) ∧
    REPred fun p : ℕ+ × ℕ × (ℤ × ℕ) =>
      ∃ Q : ElemMeasure, Q.code = p.2.1 ∧ ((ratVal p.2.2 : ℝ) : EReal) < d p.1 Q

/-- `d_F(ω | Q) = -log₂ Q({ω}) - F(ω)` (equation (12)), `+∞` when `Q({ω}) = 0`. -/
noncomputable def dF (F : ℕ+ → ℕ) (ω : ℕ+) (Q : ElemMeasure) : EReal :=
  if Q.w ω = 0 then ⊤ else ((-Real.logb 2 (Q.w ω : ℝ) - (F ω : ℝ) : ℝ) : EReal)

/-- The e-deficiency `d_e(ω | Q) = -log₂ Q({ω}) - K(ω | Q)` (equation (11)),
`+∞` when `Q({ω}) = 0`. -/
noncomputable def de (U : OptimalPrefixDecoder) (ω : ℕ+) (Q : ElemMeasure) : EReal :=
  if Q.w ω = 0 then ⊤ else
    ((-Real.logb 2 (Q.w ω : ℝ) : ℝ) : EReal) - toEReal (KobjGivenMeas U ω Q)

/-- The finite-set restriction `d^set` of a deficiency: `d(ω | Q)` when `Q = U_Ω` for a
nonempty finite set `Ω`, and `+∞` otherwise. -/
noncomputable def dset (d : ℕ+ → ElemMeasure → EReal) (ω : ℕ+) (Q : ElemMeasure) : EReal :=
  open Classical in
  if ∃ (Ω : Finset ℕ+) (hΩ : Ω.Nonempty), Q = uniform Ω hΩ then d ω Q else ⊤

/-- `N_{α,β}(d)`: objects that are not `(α, β)`-quasi-stochastic w.r.t. `d`, i.e. there is
no elementary probability measure `Q` with `K(Q) ≤ α` and `d(ω | Q) ≤ β`. -/
def nonQuasiStochastic (U : OptimalPrefixDecoder) (d : ℕ+ → ElemMeasure → EReal)
    (α : ℕ) (β : ℝ) : Set ℕ+ :=
  {ω | ¬ ∃ Q : ElemMeasure, Kmeas U Q ≤ (α : ℕ∞) ∧ d ω Q ≤ ((β : ℝ) : EReal)}

end UniversalNonstochastic.Main


