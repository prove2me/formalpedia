-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
-- name    : MomentPolytopes_QuantumFunctionals_MirrorDescent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:04:20.370347+00:00
-- url     : https://prove2.me/theorems/7c5c36ef-a87f-42ca-8f09-b34282d334bc
-- title:
--   Objective class (ϕ1)–(ϕ3), L-smoothness, Φ = ϕ∘spec with its Hilbert–Schmidt gradient, Hadamard mirror descent (6.34) and the step-size condition (6.17)
-- statement:
--   Let $\phi:\mathbb R^{n_1}\times\dots\times\mathbb R^{n_d}\to\overline{\mathbb R}=\mathbb R\cup\{\infty\}$. It satisfies **(ϕ1)–(ϕ3)** if
--   (ϕ1) $\phi$ is lower semicontinuous and convex;
--   (ϕ2) $\phi(P_1p_1,\dots,P_dp_d)=\phi(p_1,\dots,p_d)$ for all permutation matrices $P_\ell$;
--   (ϕ3) $\operatorname{dom}\phi=\{\phi<\infty\}$ has nonempty interior and $\phi$ is differentiable on $\operatorname{int}\operatorname{dom}\phi$.
--   It is **$L$-smooth** if it is finite-valued with $L$-Lipschitz (Euclidean) gradient.
--
--   Its unitarily invariant extension is $\Phi=\phi\circ\operatorname{spec}$ on $H=\mathrm{Herm}(n_1)\times\dots\times\mathrm{Herm}(n_d)$, and $\nabla\Phi(X)=(\nabla_1\Phi(X),\dots,\nabla_d\Phi(X))\in H$ is its Euclidean gradient for the Hilbert–Schmidt inner product: $\operatorname{tr}[\nabla_\ell\Phi(X)\,Y]$ is the derivative of $\Phi$ at $X$ in the direction $Y\in\mathrm{Herm}(n_\ell)$ placed in slot $\ell$.
--
--   **Hadamard mirror descent** for the tensor action, with step size $\eta>0$ and arbitrary scalars $c_k\in\mathbb C^\times$:
--   $$T_{k+1}=c_{k+1}\Big(I\otimes\bigotimes_{\ell=1}^d e^{-\frac\eta2\nabla_\ell\Phi(\mu(T_k))}\Big)T_k,\qquad T_0=c_0T .$$
--   A sequence $(v_k)$ with scalars $(c_k)$ satisfies the **step-size condition** if for all $k\in\mathbb N$
--   $$\Phi(\mu(v_k))-\Phi(\mu(v_{k+1}))-\operatorname{tr}[\mu(v_k)\nabla\Phi(\mu(v_k))]\ \ge\ \frac1\eta\log\frac{\|v_{k+1}\|^2}{|c_{k+1}|^2\|v_k\|^2},$$
--   with $\operatorname{tr}[\mu\nabla\Phi]=\sum_\ell\operatorname{tr}[\mu_\ell\nabla_\ell\Phi]$.
--
--   **Formalization Note** $\phi$ is `EReal`-valued with the hypothesis $\phi\ne-\infty$ everywhere; convexity is convexity of the epigraph $\{(p,r)\mid\phi(p)\le r\}$; differentiability and gradients refer to the real function `(ϕ p).toReal`, which agrees with $\phi$ on its domain. $\nabla_\ell\Phi(X)$ is read off from the directional derivatives along the basis $E_{aa}$, $E_{ab}+E_{ba}$, $iE_{ab}-iE_{ba}$ of $\mathrm{Herm}(n_\ell)$. $\Phi$ enters the step-size condition as a real number; it is evaluated only at moment-map values whose spectra lie in $\operatorname{int}\operatorname{dom}\phi$, where $\phi$ is finite. Nonzero $c_k$ and $\eta>0$ are hypotheses where the definitions are used.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), Example 3.7, p. 19; §3.1 and fn. 20, p. 16; Proposition 3.6, p. 18; eq. (6.17), p. 33; eq. (6.34), p. 44

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- Effective domain `dom ϕ = {p | ϕ(p) < ∞}`. -/
def effDom (ϕ : SpecTuple n → EReal) : Set (SpecTuple n) :=
  {p | ϕ p < ⊤}

/-- The objective class (ϕ1)–(ϕ3) of Example 3.7 (p. 19) for
`ϕ : ℝ^{n_1} × ⋯ × ℝ^{n_d} → ℝ̄ = ℝ ∪ {∞}` (encoded in `EReal`, never `-∞`):
(ϕ1) lower semicontinuous and convex (convex epigraph);
(ϕ2) symmetric in each argument under permutations of its entries;
(ϕ3) `dom ϕ` has nonempty interior and `ϕ` is differentiable on `int dom ϕ`. -/
structure IsAdmissibleObjective (ϕ : SpecTuple n → EReal) : Prop where
  ne_bot : ∀ p, ϕ p ≠ ⊥
  lowerSemicontinuous : LowerSemicontinuous ϕ
  convex_epigraph : Convex ℝ {q : SpecTuple n × ℝ | ϕ q.1 ≤ (q.2 : EReal)}
  symmetric : ∀ (σ : (ℓ : Fin d) → Equiv.Perm (Fin (n ℓ))) (p : SpecTuple n),
    ϕ (fun ℓ => p ℓ ∘ σ ℓ) = ϕ p
  interior_nonempty : (interior (effDom ϕ)).Nonempty
  differentiableOn : DifferentiableOn ℝ (fun p => (ϕ p).toReal) (interior (effDom ϕ))

/-- Euclidean gradient `∇ϕ(p)`, component `(ℓ, i)` = `∂ϕ/∂p_{ℓ,i}` (partial derivatives of the
real-valued function `ϕ` on the interior of its domain). -/
noncomputable def eucGrad (ϕ : SpecTuple n → EReal) (p : SpecTuple n) : SpecTuple n :=
  fun ℓ i => fderiv ℝ (fun q : SpecTuple n => (ϕ q).toReal) p
    (Pi.single (M := fun ℓ' => Fin (n ℓ') → ℝ) ℓ (Pi.single i 1))

/-- Euclidean norm `(∑_ℓ ∑_i p_{ℓ,i}²)^{1/2}` on `ℝ^{n_1} × ⋯ × ℝ^{n_d}`. -/
noncomputable def eucNorm (p : SpecTuple n) : ℝ :=
  Real.sqrt (∑ ℓ, ∑ i, p ℓ i ^ 2)

/-- `ϕ` is `L`-smooth (§3.1 and fn. 20, p. 16): finite-valued, differentiable, with an
`L`-Lipschitz gradient for the Euclidean norm. -/
def IsLSmooth (ϕ : SpecTuple n → EReal) (L : ℝ) : Prop :=
  (∀ p, ϕ p ≠ ⊤) ∧ Differentiable ℝ (fun p => (ϕ p).toReal) ∧
    ∀ p q, eucNorm (eucGrad ϕ p - eucGrad ϕ q) ≤ L * eucNorm (p - q)

/-- The unitarily invariant extension `Φ = ϕ ∘ spec` on `H = Herm(n_1) × ⋯ × Herm(n_d)`
(Proposition 3.6, p. 18), as a real number; it is evaluated only where `ϕ` is finite. -/
noncomputable def PhiR (ϕ : SpecTuple n → EReal) (X : MatTuple n) : ℝ :=
  (ϕ (specTuple X)).toReal

/-- Directional derivative `DΦ(X)[Y]` of `Φ` at `X` along the `ℓ`-th component direction `Y`. -/
noncomputable def dirDeriv (ϕ : SpecTuple n → EReal) (X : MatTuple n) (ℓ : Fin d)
    (Y : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ) : ℝ :=
  deriv (fun t : ℝ => PhiR ϕ (Function.update X ℓ (X ℓ + (t : ℂ) • Y))) 0

/-- The Euclidean gradient `∇Φ(X) = (∇_1Φ(X), …, ∇_dΦ(X)) ∈ H` of `Φ` for the Hilbert–Schmidt
inner product (p. 31, (6.8): "∇Φ denotes the usual Euclidean gradient"): the Hermitian tuple
with `tr[∇_ℓΦ(X) Y] = DΦ(X)[Y]` for Hermitian `Y` in the `ℓ`-th slot, read off on the basis
`E_aa`, `E_ab + E_ba`, `i E_ab − i E_ba` of `Herm(n_ℓ)`. -/
noncomputable def hsGrad (ϕ : SpecTuple n → EReal) (X : MatTuple n) : MatTuple n :=
  fun ℓ a b =>
    if a = b then ((dirDeriv ϕ X ℓ (Matrix.single a a 1) : ℝ) : ℂ)
    else (((dirDeriv ϕ X ℓ (Matrix.single a b 1 + Matrix.single b a 1) : ℝ) : ℂ) +
      Complex.I * ((dirDeriv ϕ X ℓ
        (Matrix.single a b Complex.I - Matrix.single b a Complex.I) : ℝ) : ℂ)) / 2

/-- Hadamard mirror descent for the tensor action (eq. (6.34), p. 44):
`T_{k+1} = c_{k+1} (I ⊗ ⊗_ℓ e^{-(η/2) ∇_ℓΦ(µ(T_k))}) T_k`, `T_0 = c_0 T`, with arbitrary
scalars `c_k ∈ ℂ^×` (nonzero-ness is a hypothesis where used). -/
noncomputable def mirrorDescentSeq (ϕ : SpecTuple n → EReal) (η : ℝ) (c : ℕ → ℂ)
    (T : Ten d n0 n) : ℕ → Ten d n0 n
  | 0 => c 0 • T
  | k + 1 => c (k + 1) •
      act (fun ℓ => hermExp (-(η / 2)) (hsGrad ϕ (momentMap (mirrorDescentSeq ϕ η c T k)) ℓ))
        (mirrorDescentSeq ϕ η c T k)

/-- The step-size condition (6.17), p. 33, for a sequence `(v_k)` with scalars `(c_k)`:
for all `k ∈ ℕ`,
`Φ(µ(v_k)) − Φ(µ(v_{k+1})) − tr[µ(v_k) ∇Φ(µ(v_k))] ≥ (1/η) log(‖v_{k+1}‖² / (|c_{k+1}|² ‖v_k‖²))`,
where `tr[µ ∇Φ] = ∑_ℓ tr[µ_ℓ ∇_ℓΦ]` (a real number). -/
def StepSizeCondition (ϕ : SpecTuple n → EReal) (η : ℝ) (v : ℕ → Ten d n0 n) (c : ℕ → ℂ) :
    Prop :=
  ∀ k : ℕ,
    PhiR ϕ (momentMap (v k)) - PhiR ϕ (momentMap (v (k + 1))) -
        ∑ ℓ, (Matrix.trace (momentMap (v k) ℓ * hsGrad ϕ (momentMap (v k)) ℓ)).re ≥
      (1 / η) * Real.log (tnorm (v (k + 1)) ^ 2 / (‖c (k + 1)‖ ^ 2 * tnorm (v k) ^ 2))

end MomentPolytopes.QuantumFunctionals


