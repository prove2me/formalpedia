-- Prove2me | Definitions.Def_Hairer_Model
-- name    : Hairer_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:37:06.054296+00:00
-- url     : https://prove2.me/theorems/7f6c13df-1d08-4bc9-9451-7460c02958d6
-- title:
--   Models for a regularity structure and modelled distributions
-- statement:
--   Models and the spaces $\mathcal{D}^\gamma$.
--
--   A **model** $(\Pi,\Gamma)$ for a regularity structure on $\mathbb{R}^d$ with scaling $s$
--   (Definition 2.17) consists of maps $\Gamma_{xy} \in G$ and linear maps
--   $\Pi_x : T \to \mathcal{D}'$ satisfying the algebraic identities $\Gamma_{xx} = \mathrm{id}$,
--   $\Gamma_{xy}\Gamma_{yz} = \Gamma_{xz}$ and $\Pi_y = \Pi_x \circ \Gamma_{xy}$, together with
--   the analytic bounds (2.15): for every $\gamma>0$ and every compact $K$ there is a constant $C$
--   with
--   $$ |(\Pi_x a)(S^{\delta}_{s,x}\varphi)| \le C\,\|a\|\,\delta^{\ell}, \qquad
--   \|Q_m \Gamma_{xy} a\| \le C\,\|a\|\,\|x-y\|_s^{\ell-m}, $$
--   uniformly over $x,y \in K$, $\delta \in (0,1]$, test functions
--   $\varphi \in \mathcal{B}^r_{s,0}$, homogeneities $\ell \in A$ with $\ell<\gamma$, $m<\ell$ and
--   $a \in T_\ell$. As in Hairer, $r$ is the smallest natural number with $\ell > -r$ for every
--   $\ell \in A$; this requirement is part of the definition (`IsTestOrder`).
--
--   A **modelled distribution** of order $\gamma$ (Definition 3.1) is a function
--   $f : \mathbb{R}^d \to T_{<\gamma}$ such that on every compact $K$ both
--   $\|f(x)\|_\beta$ and
--   $\|f(x)-\Gamma_{xy}f(y)\|_\beta / \|x-y\|_s^{\gamma-\beta}$
--   are bounded, uniformly over $x,y \in K$ with $\|x-y\|_s \le 1$ and over $\beta \in A$ with
--   $\beta<\gamma$; this is the finiteness of $|||f|||_{\gamma;K}$. `TakesValuesIn V f` expresses
--   that $f$ takes values in a sector $V$, so that `IsModelled` together with it describes
--   $\mathcal{D}^\gamma(V)$.
--
--   `truncProd` is the truncated pointwise product (4.3),
--   $(f \star_\gamma g)(x) = \sum_{m+n<\gamma} Q_m f(x) \star Q_n g(x)$.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Definition 2.17 with the bounds (2.15) (p. 25), Definition 3.1 with (3.1) (p. 30), and the truncated product (4.3) (p. 49)

import Definitions.Def_Hairer_RegularityStructure

/-!
# Models and modelled distributions

Formalisation of

  M. Hairer, *A theory of regularity structures*, Invent. Math. 198 (2014) 269–504,
  arXiv:1303.5113:

Definition 2.17 (a model `(Π, Γ)` for a regularity structure, with the analytic bounds
(2.15)), Definition 3.1 (the spaces `D^γ` of modelled distributions and `D^γ(V)` for a
sector `V`), and the truncated pointwise product (4.3) of modelled distributions.
-/

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

variable {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
  [∀ a : A, NormedSpace ℝ (E a)]

/-- `r` is the smallest natural number such that `ℓ > -r` for every `ℓ ∈ A`; this is the
order of the test functions used in Hairer's Definition 2.17. -/
def IsTestOrder (A : Set ℝ) (r : ℕ) : Prop :=
  (∀ ℓ ∈ A, -(r : ℝ) < ℓ) ∧ ∀ r' : ℕ, (∀ ℓ ∈ A, -(r' : ℝ) < ℓ) → r ≤ r'

/-- **Definition 2.17 (Hairer).** A *model* for the regularity structure `(A, T, G)` on
`ℝ^d` with scaling `s` consists of maps `Γ : ℝ^d × ℝ^d → G` and
`Π : ℝ^d → (T → 𝒟')` such that `Γ_{xx} = id`, `Γ_{xy} Γ_{yz} = Γ_{xz}`,
`Π_y = Π_x ∘ Γ_{xy}`, and such that for every `γ > 0` and every compact `K` the
bounds (2.15)
`|(Π_x a)(S^δ_{s,x} φ)| ≤ C ‖a‖ δ^ℓ` and `‖Γ_{xy} a‖_m ≤ C ‖a‖ ‖x-y‖_s^{ℓ-m}`
hold uniformly over `x, y ∈ K`, `δ ∈ (0,1]`, `φ ∈ B^r_{s,0}`, `ℓ ∈ A` with `ℓ < γ`,
`m < ℓ` and `a ∈ T_ℓ`. -/
structure IsModel {d : ℕ} (s : Fin d → ℕ) (r : ℕ)
    (G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E))
    (Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) : Prop where
  /-- `r` is the order of test functions attached to `A`. -/
  testOrder : IsTestOrder A r
  /-- `Γ_{xy}` is an element of the structure group. -/
  gam_mem : ∀ x y : Pt d, Gam x y ∈ G
  /-- `Γ_{xx}` is the identity. -/
  gam_self : ∀ (x : Pt d) (τ : ModelSpace A E), Gam x x τ = τ
  /-- `Γ_{xy} Γ_{yz} = Γ_{xz}`. -/
  gam_comp : ∀ (x y z : Pt d) (τ : ModelSpace A E), Gam x y (Gam y z τ) = Gam x z τ
  /-- `Π_y = Π_x ∘ Γ_{xy}`. -/
  pi_comp : ∀ (x y : Pt d) (τ : ModelSpace A E), Pi y τ = Pi x (Gam x y τ)
  /-- The analytic bound on `Π`, first half of (2.15). -/
  pi_bound : ∀ γ : ℝ, 0 < γ → ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
    ∀ ℓ : A, (ℓ : ℝ) < γ → ∀ a : E ℓ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(Pi x (incl ℓ a)).eval (scaledTest s δ x η)| ≤ C * ‖a‖ * δ ^ (ℓ : ℝ)
  /-- The analytic bound on `Γ`, second half of (2.15). -/
  gam_bound : ∀ γ : ℝ, 0 < γ → ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
    ∀ ℓ m : A, (ℓ : ℝ) < γ → (m : ℝ) < (ℓ : ℝ) → ∀ a : E ℓ, ∀ x ∈ K, ∀ y ∈ K,
      ‖proj m (Gam x y (incl ℓ a))‖ ≤ C * ‖a‖ * snorm s (x - y) ^ ((ℓ : ℝ) - (m : ℝ))

/-- **Definition 3.1 (Hairer).** The space `D^γ` of *modelled distributions*: functions
`f : ℝ^d → T_{<γ}` such that, for every compact `K`, the quantity
`|||f|||_{γ;K} = sup_{x ∈ K, β < γ} ‖f(x)‖_β +
  sup_{x,y ∈ K, ‖x-y‖_s ≤ 1, β < γ} ‖f(x) - Γ_{xy} f(y)‖_β / ‖x-y‖_s^{γ-β}`
is finite. -/
structure IsModelled {d : ℕ} (s : Fin d → ℕ) (γ : ℝ)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)
    (f : Pt d → ModelSpace A E) : Prop where
  /-- `f` takes values in `T_{<γ}`. -/
  vanishing : ∀ (x : Pt d) (a : A), γ ≤ (a : ℝ) → proj a (f x) = 0
  /-- Local boundedness and the Hölder-type bound of (3.1). -/
  bound : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
    (∀ x ∈ K, ∀ b : A, (b : ℝ) < γ → ‖proj b (f x)‖ ≤ C) ∧
    (∀ x ∈ K, ∀ y ∈ K, snorm s (x - y) ≤ 1 → ∀ b : A, (b : ℝ) < γ →
      ‖proj b (f x - Gam x y (f y))‖ ≤ C * snorm s (x - y) ^ (γ - (b : ℝ)))

/-- `f` takes values in the sector `V`; together with `IsModelled` this describes the
space `D^γ(V)` of Hairer. -/
def TakesValuesIn (V : ∀ a : A, Submodule ℝ (E a)) {d : ℕ}
    (f : Pt d → ModelSpace A E) : Prop := ∀ x : Pt d, f x ∈ sectorSpace V

/-- The truncated pointwise product (4.3) of Hairer:
`(f ⋆_γ g)(x) = ∑_{m+n<γ} Q_m f(x) ⋆ Q_n g(x)`. -/
def truncProd {d : ℕ} (γ : ℝ)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (f g : Pt d → ModelSpace A E) : Pt d → ModelSpace A E := fun x =>
  ∑ m ∈ (f x).support, ∑ n ∈ (g x).support,
    if (m : ℝ) + (n : ℝ) < γ then star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0

end Hairer


