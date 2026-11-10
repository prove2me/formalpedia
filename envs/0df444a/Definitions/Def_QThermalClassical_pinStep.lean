-- Prove2me | Definitions.Def_QThermalClassical_pinStep
-- name    : QThermalClassical_pinStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:35.99777+00:00
-- url     : https://prove2.me/theorems/a60d5f69-aef0-43ad-8504-cf8c03ed85c1
-- title:
--   One iteration of Algorithm 1 (ITERATIVE PINNING)
-- statement:
--   One pass of the while loop of **Algorithm 1** (p.27), given the unpinned sites $S$, the configuration $\chi$, a choice of $a^*$, two sampled outcomes $(b_1,E_1)$, $(b_2,E_2)$ and a branch $J\in\{1,\dots,7\}$:
--   1. If $\chi$ is nonempty and $u_S(X_l)\neq\emptyset$, the working monomial is $(c_l,X_l)$ and $a^*$ must lie in $u_S(X_l)$; otherwise $(0,I)$ is appended and becomes the working monomial, and $a^*$ is any element of $A(S)$ (lines 3–6).
--   2. The working monomial $(c,X)$ is replaced by (lines 11–25), with $p_1=q$ and $p_J=(1-q)/6$ for $J\neq1$:
--   $$
--   \begin{aligned}
--   &J=1:\ (c/p_1,\ X);\quad J=2:\ (b_1/p_2,\ (E_1+E_1^\dagger)/2);\quad J=3:\ (b_2/p_3,\ (E_2+E_2^\dagger)/2);\\
--   &J=4:\ (b_1c/p_4,\ (E_1^\dagger X+XE_1)/2);\quad J=5:\ (b_2c/p_5,\ (E_2^\dagger X+XE_2)/2);\\
--   &J=6:\ (b_1b_2/p_6,\ (E_1^\dagger E_2+E_2^\dagger E_1)/2);\quad J=7:\ (b_1b_2c/p_7,\ (E_2^\dagger XE_1+E_1^\dagger XE_2)/2),
--   \end{aligned}
--   $$
--   with term lists by (79); if the new monomial is $0$ it is reset to $(0,I)$ (line 26).
--   3. $S\leftarrow S\setminus\mathrm{supp}(P_{a^*})$ (line 27).
--
--   Admissible choices of $a^*$ and the branch probabilities $p_J$ are separate definitions.
--
--   **Formalization Note** The nondeterministic choice of $a^*$ and the random samples are inputs, so statements quantify over them; the paper's $J$ is the index plus one. The full algorithm is transcribed in the docstring.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_Config
import Definitions.Def_QThermalClassical_Sampler

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The probability `p_J` of branch `J` in line 10 of Algorithm 1: `p_1 = q`,
`p_J = (1 − q)/6` for `J ≠ 1`. The paper's branch `J ∈ {1, …, 7}` is `J.val + 1`. -/
noncomputable def pJ (q : ℝ) (J : Fin 7) : ℝ :=
  if J = 0 then q else (1 - q) / 6

/-- Admissible choices of `a*` in lines 3–6 of Algorithm 1: if the configuration is nonempty
and `u_S(X_l) ≠ ∅` for its last monomial, any `â ∈ u_S(X_l)`; otherwise any element of
`A(S)`. -/
def IsAdmissible (c : PauliWord Q → ℝ) (S : Finset Q) (χ : Config Q) (a : PauliWord Q) :
    Prop :=
  match χ.getLast? with
  | some e => if (uSet S e.terms).Nonempty then a ∈ uSet S e.terms else a ∈ termsIn c S
  | none => a ∈ termsIn c S

/-- Lines 11–25 of Algorithm 1: the new pair `(ĉ, X̂)` (and term list) computed from the
working monomial `(c_l̂, X_l̂)` and the two sampled outcomes `(b₁, E₁)`, `(b₂, E₂)`, for branch
`J` (paper index `J.val + 1`):
* `J = 1`: `((1/p₁) c, X)`;
* `J = 2`: `((1/p₂) b₁, (E₁ + E₁^†)/2)`; `J = 3`: `((1/p₃) b₂, (E₂ + E₂^†)/2)`;
* `J = 4`: `((1/p₄) b₁ c, (E₁^† X + X E₁)/2)`; `J = 5`: `((1/p₅) b₂ c, (E₂^† X + X E₂)/2)`;
* `J = 6`: `((1/p₆) b₁ b₂, (E₁^† E₂ + E₂^† E₁)/2)`;
* `J = 7`: `((1/p₇) b₁ b₂ c, (E₂^† X E₁ + E₁^† X E₂)/2)`.
The term lists follow (79). -/
noncomputable def pinUpdate (q : ℝ) (J : Fin 7) (o₁ o₂ : Outcome Q) (e : Monomial Q) : Monomial Q :=
  let p := pJ q J
  let h : ℂ := 1 / 2
  if J.val = 0 then ⟨e.coeff / p, e.op, e.terms⟩
  else if J.val = 1 then ⟨o₁.b / p, h • (o₁.E + o₁.E.conjTranspose), o₁.C⟩
  else if J.val = 2 then ⟨o₂.b / p, h • (o₂.E + o₂.E.conjTranspose), o₂.C⟩
  else if J.val = 3 then
    ⟨o₁.b * e.coeff / p, h • (o₁.E.conjTranspose * e.op + e.op * o₁.E), e.terms ++ o₁.C⟩
  else if J.val = 4 then
    ⟨o₂.b * e.coeff / p, h • (o₂.E.conjTranspose * e.op + e.op * o₂.E), e.terms ++ o₂.C⟩
  else if J.val = 5 then
    ⟨o₁.b * o₂.b / p, h • (o₁.E.conjTranspose * o₂.E + o₂.E.conjTranspose * o₁.E), o₁.C ++ o₂.C⟩
  else
    ⟨o₁.b * o₂.b * e.coeff / p,
      h • (o₂.E.conjTranspose * e.op * o₁.E + o₁.E.conjTranspose * e.op * o₂.E),
      e.terms ++ o₁.C ++ o₂.C⟩

open Classical in
/-- Line 26 of Algorithm 1: a monomial with `X̂ = 0` is replaced by `(0, I)` (empty term
list). -/
noncomputable def resetIfZero (e : Monomial Q) : Monomial Q :=
  if e.op = 0 then ⟨0, 1, []⟩ else e

/-- One iteration of the while loop of Algorithm 1 (ITERATIVE PINNING), p.27, for a given
choice of `a*`, sampled outcomes `(b₁, E₁)`, `(b₂, E₂)` and branch `J`; it returns the new set
of unpinned sites `Ŝ = S \ supp(P_{a*})` (line 27) and the new configuration `χ̂`.

Algorithm 1 (transcribed from p.27). Require: Hamiltonian `H = Σ_a h_a = Σ_a λ_a P_a` and a
sampling primitive satisfying `E[I + bE] = e^{−ηH(S)} e^{η(H(S) − H^{(S)}_{(a*)})}` with
`|b| ≤ L(η) q^t`. Ensure: a configuration `χ` with `E[σ(χ)] = e^{−βH}`.
1. `S = Λ, χ = ∅, l = 0`.
2. while `A(S) ≠ ∅` do
3. if `l ≥ 1` and `∃ â ∈ u_S(X_l)` then
4. `a* ← â` and set `l̂ ← l`
5. else
6. `c_{l+1} ← 0, X_{l+1} ← I`, add `(c_{l+1}, X_{l+1})` to `χ`, `l̂ ← l + 1`, set `a*` to any
   element in `A(S)`.
8.–9. Sample `b₁, E₁` and `b₂, E₂` with `η → β/2`, `H → H(S)`, and selected label `a*` so
   that `E[I + bᵢEᵢ] = e^{−(β/2)H(S)} e^{(β/2)(H(S) − H^{(S)}_{(a*)})}`.
10. Sample `J ∈ {1, …, 7}` with probabilities `p₁ = q`, `p_{≠1} = (1 − q)/6`.
11.–25. Update `(ĉ, X̂)` by branch `J` (see `pinUpdate`).
26. Set `c_l̂ ← ĉ, X_l̂ ← X̂`; if `X̂ = 0`, set `(c_l̂, X_l̂)` to `(0, I)`.
27. `l ← l̂, S ← S \ a*`.
29. return `χ`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Algorithm 1, p.27.

**Formalization Note.** The choice of `a*` (line 6: "any element") and the sampled values are
inputs; the admissibility of `a*` is `IsAdmissible`, and the distribution of the samples is
handled by `HasStepExpect`. `S \ a*` is `S \ supp(P_{a*})`, as on p.13. -/
noncomputable def pinStep (q : ℝ) (S : Finset Q) (χ : Config Q) (a : PauliWord Q)
    (o₁ o₂ : Outcome Q) (J : Fin 7) : Finset Q × Config Q :=
  let χ' : Config Q :=
    match χ.getLast? with
    | some e => if (uSet S e.terms).Nonempty then χ else χ ++ [⟨0, 1, []⟩]
    | none => χ ++ [⟨0, 1, []⟩]
  let e : Monomial Q := χ'.getLast?.getD ⟨0, 1, []⟩
  (S \ pauliSupport a, χ'.dropLast ++ [resetIfZero (pinUpdate q J o₁ o₂ e)])

end QThermalClassical


