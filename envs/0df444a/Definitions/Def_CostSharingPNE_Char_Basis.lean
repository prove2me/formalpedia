-- Prove2me | Definitions.Def_CostSharingPNE_Char_Basis
-- name    : CostSharingPNE_Char_Basis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:45.580584+00:00
-- url     : https://prove2.me/theorems/cfc93dac-5737-494b-b9a4-8d735891ffa8
-- title:
--   §3 and Appendix A — inclusion functions, contributing coalitions 𝒯^W, 𝒯(S), N(S), 𝒯_ij, the basis rules (27), 𝒯^+_ij (53), minimal elements and the relations (74)
-- statement:
--   Fix a welfare function $W$ on the players $N$.
--
--   1. The **inclusion function** of $T\subseteq N$ is $W^T(S)=1$ if $T\subseteq S$ and $0$ otherwise.
--   2. The **contributing coalitions** are $\mathcal T^W=\{T\neq\emptyset: q^W_T\neq 0\}$, with $q^W_T$ the basis coefficient. For $S\subseteq N$, $\mathcal T^W(S)=\{T\in\mathcal T^W: T\subseteq S\}$, the **contributing players** are $N^W(S)=\bigcup\mathcal T^W(S)$, and for players $i,j$, $\mathcal T^W_{ij}=\{T\in\mathcal T^W:\{i,j\}\subseteq T\}$.
--   3. Given a distribution rule $f$ for $W$, the **basis distribution rules** $\{f^T\}_{T\in\mathcal T}$ are defined recursively by (27): for all $S\subseteq N$ and $i\in N$,
--   $$
--   f^T(i,S)=\begin{cases}\dfrac1{q_T}\Bigl(f(i,T)-\displaystyle\sum_{T'\in\mathcal T(T)-\{T\}}q_{T'}\,f^{T'}(i,S)\Bigr), & T\subseteq S,\\[1ex] 0,&\text{otherwise.}\end{cases}
--   $$
--   4. $\mathcal T^{+}_{ij}=\{T\in\mathcal T_{ij}: f^T(i,T)>0\text{ or }f^T(j,T)>0\}$ (53), and for a collection $\mathcal B$ of sets, $\mathcal B^{\min}=\{B\in\mathcal B: \nexists B'\in\mathcal B,\ B'\subsetneq B\}$.
--   5. For a set $\mathbb W$ of welfare functions whose rules are described by weight systems $\Omega=\{\omega^{W,T}\}$, the relations (74) are: $i\succeq_\Omega j$ iff there are $W\in\mathbb W$ and $T\in\mathcal T^{W+}_{ij}$ with $i\in S_1^{W,T}$, or $i=j$; and $i=_\Omega j$ iff $i\succeq_\Omega j$ and $j\succeq_\Omega i$.
--
--   These are the tools of the proof of Theorem 1 in Appendix A: necessary conditions on $f$ are phrased through contributing coalitions, and $f$ is decomposed into the basis rules $f^T$.
--
--   **Formalization Note** $\mathcal T^W$ excludes $\emptyset$, which is Appendix A's normalization $W(\emptyset)=0$. The recursion (27) is written by well-founded recursion on $|T|$ (each $T'\in\mathcal T(T)-\{T\}$ is a proper subset of $T$); the paper orders it by the min-partition of Algorithm 1, which gives the same functions. It is meaningful only for $T\in\mathcal T^W$, where $q_T\neq0$; statements quantify over such $T$. In (74), $S_1^{W,T}$ is read on $T$ as the positive-share block $\overline T$ of $T$ under $\omega^{W,T}$, and $\mathcal T^{W+}_{ij}$ as the coalitions of $\mathcal T^W_{ij}$ in which $i$ or $j$ lies in $\overline T$; for rules described by $\Omega$ these are exactly the coalitions where $i$ or $j$ gets a positive share, as in (53).
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, (2)–(3) (p. 7), Table 4 and (16) (p. 17), (27) (p. 24), (53) (p. 35), (74) (p. 54)

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

namespace CostSharingPNE.Char

open Classical

/-- The inclusion (unanimity) function `W^T(S) = 1` if `T ⊆ S`, `0` otherwise ((2), p. 7). -/
noncomputable def unanimity {n : ℕ} (T : Finset (Fin n)) : Welfare n :=
  fun S => if T ⊆ S then 1 else 0

/-- The contributing coalitions `𝒯^W = {T ≠ ∅ : q^W_T ≠ 0}` of `W` ((3), p. 7, with the
normalization `∅ ∉ 𝒯^W` of Appendix A, p. 17). -/
noncomputable def coalitions {n : ℕ} (W : Welfare n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun T => T.Nonempty ∧ mobius W T ≠ 0)

/-- `𝒯^W(S) = {T ∈ 𝒯^W | T ⊆ S}`, the contributing coalitions in `S` (Table 4, p. 17). -/
noncomputable def coalitionsIn {n : ℕ} (W : Welfare n) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (coalitions W).filter (fun T => T ⊆ S)

/-- `N^W(S) = ⋃ 𝒯^W(S)`, the contributing players in `S` (Table 4, p. 17). -/
noncomputable def contributing {n : ℕ} (W : Welfare n) (S : Finset (Fin n)) : Finset (Fin n) :=
  (coalitionsIn W S).biUnion id

/-- `𝒯^W_{ij} = {T ∈ 𝒯^W | {i, j} ⊆ T}` ((16), p. 17). -/
noncomputable def coalitionsPair {n : ℕ} (W : Welfare n) (i j : Fin n) :
    Finset (Finset (Fin n)) :=
  (coalitions W).filter (fun T => i ∈ T ∧ j ∈ T)

/-- The basis distribution rules `f^T` of a rule `g` for `W`, defined by the recursion (27),
p. 24: for `T ⊆ S`,
`f^T(i, S) = (1 / q_T) (g(i, T) − ∑_{T' ∈ 𝒯(T) − {T}} q_{T'} f^{T'}(i, S))`,
and `f^T(i, S) = 0` otherwise. The recursion runs over strictly smaller coalitions (the
paper orders it by the min-partition of Algorithm 1, which gives the same functions). It is
used only for `T ∈ 𝒯^W`, where `q_T ≠ 0`. -/
noncomputable def basisRule {n : ℕ} (g : Rule n) (W : Welfare n) (T : Finset (Fin n))
    (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  if T ⊆ S then
    (1 / mobius W T) *
      (g i T - ∑ T' ∈ ((coalitionsIn W T).erase T).attach,
        mobius W T'.1 * basisRule g W T'.1 i S)
  else 0
termination_by T.card
decreasing_by
  have h := T'.2
  rw [Finset.mem_erase] at h
  have hsub : T'.1 ⊆ T := (Finset.mem_filter.mp h.2).2
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, h.1⟩)

/-- `𝒯^{+}_{ij}` of (53), p. 35: the coalitions of `𝒯^W_{ij}` in which `i` or `j` gets a strictly
positive share under the basis rule `f^T` of `g`. -/
noncomputable def plusPair {n : ℕ} (g : Rule n) (W : Welfare n) (i j : Fin n) :
    Finset (Finset (Fin n)) :=
  (coalitionsPair W i j).filter (fun T => 0 < basisRule g W T i T ∨ 0 < basisRule g W T j T)

/-- `ℬ^min = {B ∈ ℬ | ∄ B' ∈ ℬ, B' ⊊ B}`, the minimal elements of `(ℬ, ⊆)` (Table 4, p. 17). -/
def minimals {n : ℕ} (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ℬ.filter (fun B => ∀ B' ∈ ℬ, ¬ B' ⊂ B)

/-- The relation `i ⪰_Ω j` of (74), p. 54, for distribution rules described by the weight
systems `Ω W T = ω^{W,T}`: there are `W ∈ 𝕎` and `T ∈ 𝒯^{W+}_{ij}` with `i ∈ S_1^{W,T}`, or
`i = j`. Here `S_1^{W,T}` is read on `T` as the positive-share block `T̄` of `T` under
`ω^{W,T}`, and `𝒯^{W+}_{ij}` as the coalitions of `𝒯^W_{ij}` in which `i` or `j` lies in `T̄`. -/
def succeq {n : ℕ} (𝕎 : Set (Welfare n)) (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (i j : Fin n) : Prop :=
  (∃ W ∈ 𝕎, ∃ T ∈ coalitionsPair W i j,
      (i ∈ tbar (Ω W T) T ∨ j ∈ tbar (Ω W T) T) ∧ i ∈ tbar (Ω W T) T) ∨ i = j

/-- The relation `i =_Ω j ⟺ (i ⪰_Ω j) ∧ (j ⪰_Ω i)` of (74), p. 54. -/
def eqOmega {n : ℕ} (𝕎 : Set (Welfare n)) (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (i j : Fin n) : Prop :=
  succeq 𝕎 Ω i j ∧ succeq 𝕎 Ω j i

end CostSharingPNE.Char


