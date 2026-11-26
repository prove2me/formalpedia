-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_104
-- name    : RPLib_FX_EtPBC_104
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:42:31.990973+00:00
-- url     : https://prove2.me/theorems/a5bb1033-19a0-5fd6-b1c0-6e5efc53d7c1
-- title:
--   Proper base change for the projective line, library file 104
-- statement:
--   File 104 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2L5c2`: S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_044
import Definitions.Def_RPLib_FX_EtPBC_047
import Definitions.Def_RPLib_FX_EtPBC_077
import Definitions.Def_RPLib_FX_EtPBC_090

/-!
# Proper base change for the projective line, library file 104

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2L5c2`: S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

end GenFl

section Obj

variable {P : Scheme.{u}}

/-- **Naturality in the sheaf.** -/
theorem extFree_comp_mk₀ (W : P.Etale) {F G : EtSh Λ P} (φ : F ⟶ G) {n : ℕ} (β : Ext.{u} (freeSh Λ W) F n) :
    extFree Λ W G n (β.comp (Ext.mk₀ φ) (add_zero n)) =
      (extFree Λ W F n β).comp (Ext.mk₀ ((res W.hom Λ).map φ)) (add_zero n) := by
  rw [extFree_apply, extFree_apply, ← Ext.comp_assoc_of_third_deg_zero, extAdjMap_comp_mk₀]

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree

* **`shapExt Λ W n hn A k : Ext_W(π^* A, Λ_W) ≃+ Ext_P(A, Λ[W])`** (adjunction `π^* ⊣ π_*`, `π_*` exact, and
  `Λ[W] ≅ π_* Λ_W`); `shapExt_apply`; **`shapExt_natural`** (naturality in `A`);
* `shapH`, `shapFree` (cohomology forms): file O2Sh3b (split for kernel time).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV

universe u

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

section Shap

variable (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (n : ℕ)
  (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n)

/-- **Naturality in the source.** -/
theorem shapExt_natural {A₀ A : EtSh Λ P} (c : A₀ ⟶ A) (k : ℕ)
    (x : Ext.{u} ((pull W.hom Λ).obj A) (unitSh Λ W.left) k) :
    shapExt Λ W n hn A₀ k ((Ext.mk₀ ((pull W.hom Λ).map c)).comp x (zero_add k)) =
      (Ext.mk₀ c).comp (shapExt Λ W n hn A k x) (zero_add k) := by
  haveI := push_preservesFiniteColimits_of_deg Λ W n hn
  rw [shapExt_apply, shapExt_apply, extAdjMap_mk₀_comp, Ext.comp_assoc_of_third_deg_zero]

end Shap

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5c2 =====
section

/-!
# S4-EtPBC-A, L5c2: the family point class `αZ` on `P¹_S` at a chart point

`c : A¹_K ⟶ P¹_K` an open chart, `z = c (a)`, `Qc = pr⁻¹ (range c)`; `D̃ₒ = D̃ ×_P Uz` (L5c1) maps into the punctured
chart `Spec K[X]_{X-a}` (`fA`, `fA_fac`), giving the Kummer class `κZ c' = fA^* ξ_a(c')` and
* **`αZ c' := ε(D̃, Ũ) ∘ θ(D̃ₒ ⟶ D̃, κZ c') ∘ Λ[D̃ ⟶ W] ∈ Ext²(Λ[Zz], Λ[W])`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

section Chart

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)

variable {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)

/-- **The family point class** `ε(D̃, Ũ) ∘ θ(D̃ₒ ⟶ D̃, κZ) ∘ Λ[D̃ ⟶ W]`. -/
def αZ (c' : Λ) : Ext (freeSh Λ (Zz K gS (c (A1pt K a)) (chart_hclA c a) W)) (freeSh Λ W) 2 :=
  (mvZ_shortExact K gS (c (A1pt K a)) (chart_hclA c a) W (Qc gS c) Λ (hQc gS c a)).extClass.comp
    ((thetaM Λ (prW (Dz K gS (c (A1pt K a)) (chart_hclA c a) W (Qc gS c))
        (opEt (Uz K gS (c (A1pt K a)) (chart_hclA c a)))) 1 (κZ gS c a W hN Λ hΛ c')).comp
      (Ext.mk₀ (freeMap Λ (opnι _ _ ≫ prW W (Zz K gS (c (A1pt K a)) (chart_hclA c a) W)))) (add_zero 1)) rfl

end Chart

end RamanujanPetersson.EtPBC.EtMV

end

end


