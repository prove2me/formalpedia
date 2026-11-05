-- Prove2me | Definitions.Def_BrionAntiAffine_CechH1
-- name    : BrionAntiAffine_CechH1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:39.001502+00:00
-- url     : https://prove2.me/theorems/a6e78ebd-eb5a-43df-b1e3-d334ce12dad8
-- title:
--   $H^1(A,\mathcal O_A)$ as a $k$-vector space, and the subspace invariant
-- statement:
--   For a $k$-scheme $A$, let $\mathcal U$ be the cover of $A$ by all its affine open subsets. The group $H^1(A,\mathcal O_A)$ is the Čech cohomology
--
--   $$\check H^1(\mathcal U,\mathcal O_A)=\frac{\{(g_{UV}) : g_{VW}-g_{UW}+g_{UV}=0\ \text{on } U\cap V\cap W\}}{\{(h_V-h_U)\}},\qquad g_{UV}\in\Gamma(U\cap V,\mathcal O_A),\ h_U\in\Gamma(U,\mathcal O_A),$$
--
--   a $k$-vector space through the structure map of $A$.
--
--   The **subspace invariant** of $\alpha:G\to A$ is the set $V(G,\alpha)$ of classes $[g]$ such that there are functions $h_U\in\Gamma(\alpha^{-1}U,\mathcal O_G)$ with
--
--   $$\alpha^\sharp(g_{UV})=h_V-h_U\quad\text{on }\alpha^{-1}(U\cap V).$$
--
--   That is, $V(G,\alpha)=\ker\bigl(\alpha^*:H^1(A,\mathcal O_A)\to H^1(G,\mathcal O_G)\bigr)$. It is the other half of the correspondence in Theorem 2.7 in characteristic $0$.
--
--   **Formalization Note** An abelian variety is separated, so $\mathcal U$ is a Leray cover and this is the sheaf cohomology group. No $H^1(G,\mathcal O_G)$ is needed: $\check H^1$ of any cover injects into $H^1$, so being a coboundary on the cover $\alpha^{-1}(U)$ is the same as vanishing in $H^1(G,\mathcal O_G)$. Mathlib's sheaf cohomology is not used, since it has no $k$-structure and no pullback to $G$ yet. The invariant is a `Set`, so that its being a subspace is part of the theorem.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.2, p.8 (H¹(A, O_A)); Proposition 2.3(iii), proof, p.9; compare Proposition 2.11, p.14

import Mathlib
import Definitions.Def_BrionAntiAffine_AntiAffineOver

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Restriction of functions between opens of a scheme. -/
def res (X : Scheme.{u}) {W W' : X.Opens} (h : W' ≤ W) : Γ(X, W) →+* Γ(X, W') :=
  (X.presheaf.map (homOfLE h).op).hom

/-- The structure map `k → Γ(A, W)` of a `k`-scheme `A` on an open `W`. -/
def scal (A : Sch k) (W : A.left.Opens) : k →+* Γ(A.left, W) :=
  (res A.left (le_top : W ≤ ⊤)).comp (constants A)

theorem res_scal (A : Sch k) {W W' : A.left.Opens} (h : W' ≤ W) (c : k) :
    res A.left h (scal A W c) = scal A W' c := by
  simp only [res, scal, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Čech `0`-cochains of `𝒪_A` for the cover of `A` by all its affine opens. -/
def C0 (A : Sch k) : Type u := ∀ U : A.left.affineOpens, Γ(A.left, U.1)

/-- Čech `1`-cochains of `𝒪_A` for the cover of `A` by all its affine opens. -/
def C1 (A : Sch k) : Type u := ∀ U V : A.left.affineOpens, Γ(A.left, U.1 ⊓ V.1)

instance (A : Sch k) : AddCommGroup (C0 A) := by unfold C0; infer_instance
instance (A : Sch k) : AddCommGroup (C1 A) := by unfold C1; infer_instance

instance (A : Sch k) : Module k (C1 A) where
  smul c g := fun U V => scal A (U.1 ⊓ V.1) c * g U V
  one_smul g := by funext U V; exact (congrArg (· * g U V) (map_one _)).trans (one_mul _)
  mul_smul a b g := by
    funext U V
    exact (congrArg (· * g U V) (map_mul _ a b)).trans (mul_assoc _ _ _)
  smul_zero c := by funext U V; exact mul_zero _
  smul_add c g h := by funext U V; exact mul_add _ _ _
  add_smul a b g := by
    funext U V
    exact (congrArg (· * g U V) (map_add _ a b)).trans (add_mul _ _ _)
  zero_smul g := by
    funext U V
    exact (congrArg (· * g U V) (map_zero _)).trans (zero_mul _)

theorem C1.smul_apply (A : Sch k) (c : k) (g : C1 A) (U V : A.left.affineOpens) :
    (c • g) U V = scal A (U.1 ⊓ V.1) c * g U V := rfl

/-- The cocycle identity `g_VW - g_UW + g_UV = 0` on `U ∩ V ∩ W`. -/
def IsCocycle {A : Sch k} (g : C1 A) : Prop :=
  ∀ U V W : A.left.affineOpens,
    res A.left (W' := U.1 ⊓ V.1 ⊓ W.1) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (g V W)
      - res A.left (W' := U.1 ⊓ V.1 ⊓ W.1) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (g U W)
      + res A.left (W' := U.1 ⊓ V.1 ⊓ W.1) inf_le_left (g U V) = 0

/-- The coboundary `(δ h)_UV = h_V - h_U` on `U ∩ V`. -/
def coboundary {A : Sch k} (h : C0 A) : C1 A := fun U V =>
  res A.left (inf_le_right : U.1 ⊓ V.1 ≤ V.1) (h V) - res A.left (inf_le_left : U.1 ⊓ V.1 ≤ U.1) (h U)

/-- Čech `1`-cocycles, as a `k`-subspace of the cochains. -/
def Z1 (A : Sch k) : Submodule k (C1 A) where
  carrier := {g | IsCocycle g}
  zero_mem' := by
    intro U V W
    change res A.left _ 0 - res A.left _ 0 + res A.left _ 0 = 0
    simp
  add_mem' := by
    intro g g' hg hg' U V W
    have h1 := hg U V W
    have h2 := hg' U V W
    change res A.left _ (g V W + g' V W) - res A.left _ (g U W + g' U W)
      + res A.left _ (g U V + g' U V) = 0
    simp only [map_add]
    linear_combination h1 + h2
  smul_mem' := by
    intro c g hg U V W
    have h1 := hg U V W
    change res A.left _ (scal A _ c * g V W) - res A.left _ (scal A _ c * g U W)
      + res A.left _ (scal A _ c * g U V) = 0
    simp only [map_mul, res_scal]
    linear_combination (scal A _ c) * h1

/-- Čech `1`-coboundaries, as a `k`-subspace of the cochains. -/
def B1 (A : Sch k) : Submodule k (C1 A) where
  carrier := Set.range coboundary
  zero_mem' := ⟨0, by
    funext U V
    change res A.left _ 0 - res A.left _ 0 = 0
    simp⟩
  add_mem' := by
    rintro _ _ ⟨h, rfl⟩ ⟨h', rfl⟩
    refine ⟨h + h', ?_⟩
    funext U V
    change res A.left _ (h V + h' V) - res A.left _ (h U + h' U)
      = (res A.left _ (h V) - res A.left _ (h U)) + (res A.left _ (h' V) - res A.left _ (h' U))
    simp only [map_add]
    ring
  smul_mem' := by
    rintro c _ ⟨h, rfl⟩
    refine ⟨fun U => scal A U.1 c * h U, ?_⟩
    funext U V
    change res A.left _ (scal A V.1 c * h V) - res A.left _ (scal A U.1 c * h U)
      = scal A (U.1 ⊓ V.1) c * (res A.left _ (h V) - res A.left _ (h U))
    simp only [map_mul, res_scal]
    ring

/-- `H¹(A, 𝒪_A)` as a `k`-vector space: Čech cohomology of `𝒪_A` for the cover of `A` by all its
affine opens, cocycles modulo coboundaries. Brion, arXiv:0710.5211v3, §2.2, p.8.

**Formalization Note.** An abelian variety is separated, so this cover is Leray and the group is the
sheaf cohomology `H¹(A, 𝒪_A)`. Mathlib's `Sheaf.H` is not used: it has no `k`-structure and no
pullback to `G` yet. -/
def CechH1 (A : Sch k) : Type u := Z1 A ⧸ (B1 A).comap (Z1 A).subtype

instance (A : Sch k) : AddCommGroup (CechH1 A) := by unfold CechH1; infer_instance
instance (A : Sch k) : Module k (CechH1 A) := by unfold CechH1; infer_instance

/-- The class of a cocycle in `CechH1`. -/
def CechH1.mk {A : Sch k} (g : Z1 A) : CechH1 A := Submodule.Quotient.mk g

/-- The invariant `V(G, α)`: classes in `H¹(A, 𝒪_A)` whose pullback to `G` vanishes, i.e.
`ker(α^* : H¹(A, 𝒪_A) → H¹(G, 𝒪_G))`. A class `[g]` lies in it when there are functions
`h_U ∈ Γ(G, α⁻¹U)` with `α^♯(g_UV) = h_V - h_U` on `α⁻¹(U ∩ V)`. A `Set`, so that its being a subspace
is part of the classification.

**Formalization Note.** This needs no `H¹(G, 𝒪_G)`: `α^♯(g)` is a coboundary on the cover `α⁻¹(U)` of
`G` exactly when `α^*[g] = 0`, since `Ȟ¹` of any cover injects into `H¹`. Theorem 2.7 of Brion,
arXiv:0710.5211v3, p.11, names no map; its proof sends `(G, α)` to the image of `γᵗ` of Proposition
2.3 for `G/T`; compare Proposition 2.11, p.14, "V is the kernel of the pull-back map". -/
def vSet {G A : Sch k} (α : G ⟶ A) : Set (CechH1 A) :=
  {u | ∃ g : Z1 A, CechH1.mk g = u ∧
    ∃ h : ∀ U : A.left.affineOpens, Γ(G.left, α.left ⁻¹ᵁ U.1),
      ∀ U V : A.left.affineOpens,
        α.left.app (U.1 ⊓ V.1) (g.1 U V) =
          res G.left (W' := α.left ⁻¹ᵁ (U.1 ⊓ V.1)) (fun _ hx => hx.2) (h V)
            - res G.left (W' := α.left ⁻¹ᵁ (U.1 ⊓ V.1)) (fun _ hx => hx.1) (h U)}

end BrionAntiAffine


