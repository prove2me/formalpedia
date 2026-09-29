-- Prove2me | Definitions.Def_GroupCohomology_ContinuousH1
-- name    : GroupCohomology_ContinuousH1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/b9eec56e-3f9c-5ace-a52b-65d44d513c3b
-- title:
--   Continuous first cohomology from level-constant 1-cocycles
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group equipped with a homomorphism $r : G \to \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`), and $M$ a representation of $G$ over $k$. A cochain $f : G \to X$ is level-constant, `IsLevelConstant₁ r f`, when there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ with $F/\mathbb Q$ finite such that $f(gs) = f(g)$ for all $g, s \in G$ with $r(s)$ in the fixing subgroup of $F$; the level-constant cochains form a $k$-submodule `levelCochains₁`. Here `levelCocycles₁ r M` is the submodule of Mathlib's inhomogeneous 1-cocycles `cocycles₁ M` consisting of those cocycles whose underlying function is level-constant, and `continuousH1 r M` is its image in `H1 M` under the projection `H1π M`: a submodule of $H^1(G,M)$, not a separately constructed quotient. The membership criterion `mem_continuousH1_iff` states that $x$ lies in it exactly when $x =$ `H1π M c` for some 1-cocycle $c$ that is level-constant, and `eq_continuousH1_of_forall_mem_iff` identifies any submodule of $H^1(G,M)$ characterised by that same criterion, written out with the intermediate field and fixing-subgroup condition spelled out, with `continuousH1 r M`; this is the hypothesis shape used by statements that take an abstract "admissible" submodule of $H^1$.
--
--   The remaining declarations are auxiliaries. `continuousH2MapHom r φ` is the $k$-linear map `continuousH2 r A →ₗ continuousH2 r B` induced by a morphism $\varphi : A \to B$ of representations of the same group, obtained from the general functoriality `continuousH2Map` along the identity of $G$. For a morphism $\varphi : A \to B$, `preimageFun φ` is a choice-based partial inverse: it sends $b$ to some preimage when one exists and to $0$ otherwise, with `apply_preimageFun` and `preimageFun_apply` recording the two expected identities (the latter for injective $\varphi$). Given in addition $\psi : B \to C$ with $\psi$ surjective, and writing $\sigma$ for a set-theoretic section of $\psi$, the connecting cochains are $\delta^0(c)(g) = \varphi^{-1}(g\,\sigma c - \sigma c)$ for $c \in C$ and $\delta^1(c)(g,h) = \varphi^{-1}\bigl(g\,\sigma(c(h)) - \sigma(c(gh)) + \sigma(c(g))\bigr)$ for $c : G \to C$, defined as `deltaCochain₀` and `deltaCochain₁` by applying `preimageFun φ` to the Mathlib differentials `d₀₁ B` and `d₁₂ B` of the lifted cochain, with `deltaCochain₀_apply` and `deltaCochain₁_apply` giving these explicit formulae.
--
--   **Relation to Mathlib.** Mathlib supplies the inhomogeneous cochain apparatus used here (`cocycles₁`, `H1`, `H1π`, `d₀₁`, `d₁₂`, and for degree two `cocycles₂`); the level-constant cochain and cocycle submodules, the resulting `continuousH1` and `continuousH2`, and their functoriality are the project's own, Mathlib having no notion of continuous cohomology of this shape.
--
--   **Where it is used.** The submodule `continuousH1 r M` is the carrier of continuous (level-constant) Galois cohomology in degree one used in the cohomological bookkeeping of the deformation-theoretic part of the argument, in particular wherever a result is stated for an arbitrary submodule of $H^1$ satisfying the level-constancy criterion. The connecting cochains provide the degree-shifting maps for short exact sequences of coefficient representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousH1.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

section carriers

variable (M : Rep k G)

def levelCocycles₁ : Submodule k (cocycles₁ M) :=
  (levelCochains₁ r M).comap (cocycles₁ M).subtype

lemma mem_levelCocycles₁_iff (c : cocycles₁ M) : c ∈ levelCocycles₁ r M ↔ IsLevelConstant₁ r c :=
  Iff.rfl

def continuousH1 : Submodule k (H1 M) :=
  (levelCocycles₁ r M).map (H1π M).hom

lemma mem_continuousH1_iff (x : H1 M) :
    x ∈ continuousH1 r M ↔ ∃ c : cocycles₁ M, IsLevelConstant₁ r c ∧ (H1π M).hom c = x := by
  simp only [continuousH1, Submodule.mem_map, mem_levelCocycles₁_iff]

lemma H1π_mem_continuousH1 {c : cocycles₁ M} (hc : IsLevelConstant₁ r c) :
    (H1π M).hom c ∈ continuousH1 r M :=
  (mem_continuousH1_iff r M _).2 ⟨c, hc, rfl⟩

lemma eq_continuousH1_of_forall_mem_iff (adm₁ : Submodule k (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : G), r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    adm₁ = continuousH1 r M := by
  ext x
  rw [hadm₁, mem_continuousH1_iff]
  rfl

end carriers

abbrev continuousH2MapHom {A B : Rep k G} (φ : A ⟶ B) : continuousH2 r A →ₗ[k] continuousH2 r B :=
  continuousH2Map (MonoidHom.id G) (fun _ => rfl) φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a)

section delta

variable {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)

open Classical in

def preimageFun (b : B) : A :=
  if h : ∃ a : A, φ.hom a = b then h.choose else 0

lemma apply_preimageFun {b : B} (h : ∃ a : A, φ.hom a = b) : φ.hom (preimageFun φ b) = b := by
  rw [preimageFun, dif_pos h]; exact h.choose_spec

lemma preimageFun_apply (hφ : Function.Injective φ.hom) (a : A) : preimageFun φ (φ.hom a) = a :=
  hφ (apply_preimageFun φ ⟨a, rfl⟩)

variable (hψ : Function.Surjective ψ.hom)

def deltaCochain₀ (c : C) : G → A :=
  fun g => preimageFun φ ((d₀₁ B).hom (Function.surjInv hψ c) g)

def deltaCochain₁ (c : G → C) : G × G → A :=
  fun p => preimageFun φ ((d₁₂ B).hom (Function.surjInv hψ ∘ c) p)

lemma deltaCochain₀_apply (c : C) (g : G) :
    deltaCochain₀ φ ψ hψ c g = preimageFun φ (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) := by
  rw [deltaCochain₀, d₀₁_hom_apply]

lemma deltaCochain₁_apply (c : G → C) (g h : G) :
    deltaCochain₁ φ ψ hψ c (g, h) = preimageFun φ
      (B.ρ g (Function.surjInv hψ (c h)) - Function.surjInv hψ (c (g * h)) + Function.surjInv hψ (c g)) := by
  rw [deltaCochain₁, d₁₂_hom_apply]; rfl

end delta

end groupCohomology

end


