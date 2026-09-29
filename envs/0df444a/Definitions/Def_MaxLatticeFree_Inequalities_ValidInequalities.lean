-- Prove2me | Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
-- name    : MaxLatticeFree_Inequalities_ValidInequalities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:45:32.025297+00:00
-- url     : https://prove2.me/theorems/2e0c3add-e316-48b9-9538-41094d532b37
-- title:
--   Valid, trivial, dominating, minimal and equivalent inequalities for $R_f(W)$; sublinear functions
-- statement:
--   Fix $f\in\mathbb R^q$ and a linear subspace $W\subseteq\mathbb R^q$, with $R_f(W)$, $V$ and $\mathcal V$ as in the relaxation model. A **linear inequality** is given by a function $\psi:W\to\mathbb R$ (arbitrary, no regularity) and $\alpha\in\mathbb R$:
--   $$\Psi(s)=\sum_{r\in W}\psi(r)s_r\ \ge\ \alpha .$$
--
--   1. It is **valid** for $R_f(W)$ if every $s\in R_f(W)$ satisfies it.
--   2. It is **trivial** if every $s\in\mathcal V$ with $s_r\ge0$ for all $r\in W$ satisfies it.
--   3. $\sum\psi(r)s_r\ge\alpha$ **dominates** $\sum\psi'(r)s_r\ge\alpha$ (same right-hand side) if $\psi(r)\le\psi'(r)$ for all $r\in W$.
--   4. A valid inequality $\sum\psi(r)s_r\ge\alpha$ is **minimal** if it is not dominated by any valid inequality $\sum\psi'(r)s_r\ge\alpha$ with $\psi'\ne\psi$. (Minimality includes validity.)
--   5. $\sigma:W\to\mathbb R$ is **positively homogeneous** if $\sigma(\lambda r)=\lambda\sigma(r)$ for all $r\in W$, $\lambda\ge0$; **subadditive** if $\sigma(r^1+r^2)\le\sigma(r^1)+\sigma(r^2)$; **sublinear** if both.
--   6. $B_\psi=\{x\in f+W\mid \psi(x-f)\le\alpha\}$, and $\{x\in f+W\mid\psi(x-f)<\alpha\}$, the set the paper calls $\operatorname{int}(B_\psi)$ for sublinear $\psi$.
--   7. $C\in\mathbb R^{\ell\times q}$, $d\in\mathbb R^\ell$ **describe $V$** if $V=\{x\in f+W\mid Cx=d\}$.
--   8. Two valid inequalities $\sum\psi(r)s_r\ge\alpha$ and $\sum\psi'(r)s_r\ge\alpha'$ are **equivalent** (with respect to $C,d$ describing $V$) if there are $\rho>0$ and $\lambda\in\mathbb R^\ell$ with
--   $$\psi(r)=\rho\,\psi'(r)+\lambda^{T}Cr\ \ (r\in W),\qquad \alpha=\rho\,\alpha'+\lambda^{T}(d-Cf).$$
--
--   Equivalent inequalities cut out the same region of $\mathcal V$, which contains $R_f(W)$; this is why, for irrational $W$, one inequality has infinitely many forms.
--
--   **Formalization Note** The equivalence predicate contains the three facts Definition 25 presupposes: $C,d$ describe $V$, and both inequalities are valid. The set $\{x\in f+W\mid\psi(x-f)<\alpha\}$ is kept separate from the topological relative interior of $B_\psi$: the paper identifies the two on p. 17, which is correct for sublinear $\psi$ when $\alpha\ne0$ but not in general at $\alpha=0$ (for $\psi\equiv0$ the relative interior of $B_\psi$ is all of $f+W$).
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 4, eq. (3); p. 5 (trivial, dominates, minimal, equivalent); p. 15, Definitions 21, 22; p. 17, Definitions 24, 25 and the set B_psi

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel

open Matrix

namespace MaxLatticeFree.Inequalities

variable {q : ℕ}

/-- The inequality `∑_{r ∈ W} ψ(r) s_r ≥ α` is valid for `R_f(W)` (arXiv:1701.06543v1, p. 4):
every `s ∈ R_f(W)` satisfies it. -/
noncomputable def IsValid (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (α : ℝ) : Prop :=
  ∀ s ∈ Rf f W, α ≤ linVal ψ s

/-- The inequality `∑_{r ∈ W} ψ(r) s_r ≥ α` is trivial (arXiv:1701.06543v1, p. 5): it is
satisfied by every `s ∈ 𝒱` with `s_r ≥ 0` for every `r ∈ W`. -/
noncomputable def IsTrivial (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (α : ℝ) : Prop :=
  ∀ s ∈ calV f W, (∀ r, 0 ≤ s r) → α ≤ linVal ψ s

/-- `∑ ψ(r) s_r ≥ α` dominates `∑ ψ'(r) s_r ≥ α` (same right-hand side `α`) if `ψ(r) ≤ ψ'(r)` for
all `r ∈ W` (arXiv:1701.06543v1, p. 15, Definition 22). -/
noncomputable def Dominates {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ ψ' : W → ℝ) : Prop :=
  ∀ r, ψ r ≤ ψ' r

/-- A valid inequality `∑ ψ(r) s_r ≥ α` is minimal (arXiv:1701.06543v1, p. 17, Definition 24): it
is valid, and it is not dominated by any valid `∑ ψ'(r) s_r ≥ α` with `ψ' ≠ ψ`. -/
noncomputable def IsMinimal (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (α : ℝ) : Prop :=
  IsValid f W ψ α ∧ ∀ ψ' : W → ℝ, IsValid f W ψ' α → Dominates ψ' ψ → ψ' = ψ

/-- Positively homogeneous (arXiv:1701.06543v1, p. 15, Definition 21). -/
noncomputable def IsPositivelyHomogeneous {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (σ : W → ℝ) : Prop :=
  ∀ (r : W) (c : ℝ), 0 ≤ c → σ (c • r) = c * σ r

/-- Subadditive (arXiv:1701.06543v1, p. 15, Definition 21). -/
noncomputable def IsSubadditive {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (σ : W → ℝ) : Prop :=
  ∀ r₁ r₂ : W, σ (r₁ + r₂) ≤ σ r₁ + σ r₂

/-- Sublinear = positively homogeneous and subadditive (arXiv:1701.06543v1, p. 15, Def. 21). -/
noncomputable def IsSublinear {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (σ : W → ℝ) : Prop :=
  IsPositivelyHomogeneous σ ∧ IsSubadditive σ

/-- `B_ψ = {x ∈ f + W | ψ(x - f) ≤ α}` (arXiv:1701.06543v1, p. 17). -/
noncomputable def Bpsi (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (α : ℝ) : Set (EuclideanSpace ℝ (Fin q)) :=
  {x | ∃ h : x - f ∈ W, ψ ⟨x - f, h⟩ ≤ α}

/-- `{x ∈ f + W | ψ(x - f) < α}`, the set the paper names `int(B_ψ)` for sublinear `ψ`
(arXiv:1701.06543v1, p. 17: "the interior of `B_ψ` is `int(B_ψ) = {x ∈ f + W : ψ(x - f) < α}`"). -/
noncomputable def intBpsi (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (α : ℝ) : Set (EuclideanSpace ℝ (Fin q)) :=
  {x | ∃ h : x - f ∈ W, ψ ⟨x - f, h⟩ < α}

/-- `C ∈ ℝ^{ℓ×q}`, `d ∈ ℝ^ℓ` describe `V` inside `f + W`: `V = {x ∈ f + W | Cx = d}`
(arXiv:1701.06543v1, p. 5 and p. 17, Definition 25). -/
noncomputable def IsAffineHullDescription {ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) :
    Prop :=
  (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) = {x | x ∈ affSpace f W ∧ C *ᵥ x.ofLp = d}

/-- Equivalence of valid inequalities (arXiv:1701.06543v1, p. 17, Definition 25): with `C, d`
such that `V = {x ∈ f + W | Cx = d}`, the valid inequalities `∑ ψ(r) s_r ≥ α` and
`∑ ψ'(r) s_r ≥ α'` are equivalent if there are `ρ > 0` and `λ ∈ ℝ^ℓ` with
`ψ(r) = ρ ψ'(r) + λᵀ C r` for all `r ∈ W` and `α = ρ α' + λᵀ (d - C f)`. -/
noncomputable def Equivalent {ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (ψ : W → ℝ) (α : ℝ) (ψ' : W → ℝ) (α' : ℝ) :
    Prop :=
  IsAffineHullDescription f W C d ∧ IsValid f W ψ α ∧ IsValid f W ψ' α' ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ lam : Fin ℓ → ℝ,
      (∀ r : W, ψ r = ρ * ψ' r + lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp)) ∧
      α = ρ * α' + lam ⬝ᵥ (d - C *ᵥ f.ofLp)

end MaxLatticeFree.Inequalities


