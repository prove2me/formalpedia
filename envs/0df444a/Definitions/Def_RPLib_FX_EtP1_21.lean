-- Prove2me | Definitions.Def_RPLib_FX_EtP1_21
-- name    : RPLib_FX_EtP1_21
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:27:45.605243+00:00
-- url     : https://prove2.me/theorems/c32a4866-8fac-5946-9938-b4cdfd29fb37
-- title:
--   Étale cohomology of the projective line, library file 21 of 34
-- statement:
--   File 21 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_39

/-!
# Étale cohomology of the projective line, library file 21 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_MV =====
section

/-!
# S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)

* `mvS F U V`: the short complex `j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F`; **`mvS_shortExact`** when `U ∪ V = X`.
* `subsingleton_ext_biprod`, **`precomp_extClass_bijective`**: `Ext` out of a biproduct; the connecting map of the
  contravariant `Ext` sequence is bijective when the middle terms vanish.
* `cutExt j G n : Ext^n(j_{U!}Λ_U, G) ≃ H^n(U, G|_U)`, `cutH j n`, `cutHOpen W n`.
* **`P1.h2Equiv`**: `H^2(P^1, Λ) ≃ H^1(U ⊓ V, Λ)` for the two standard charts, when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtGen

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]

end ExtGen

section MV

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end MV

section Cut

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

end Cut

section CutOpen

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end CutOpen

section ExtIface

variable {C : Type v} [Category.{w} C] [Abelian C]

/-- `S.ShortExact` read in the abelian structure (kernel-cheap interface for the `P^1` Mayer-Vietoris step). -/
abbrev ShortExactA (S : ShortComplex C) : Prop := S.ShortExact

variable [HasExt.{u} C]

/-- `Ext^n(S.X₁, Y)`. -/
abbrev ExtX₁ (S : ShortComplex C) (Y : C) (n : ℕ) : Type u := Ext S.X₁ Y n
/-- `Ext^n(S.X₂, Y)`. -/
abbrev ExtX₂ (S : ShortComplex C) (Y : C) (n : ℕ) : Type u := Ext S.X₂ Y n
/-- `Ext^n(S.X₃, Y)`. -/
abbrev ExtX₃ (S : ShortComplex C) (Y : C) (n : ℕ) : Type u := Ext S.X₃ Y n

/-- `Ext^2(S.X₃, Y) ≃ Ext^1(S.X₁, Y)` when `Ext^1(S.X₂, Y) = Ext^2(S.X₂, Y) = 0`. -/
def mvEquivGen {S : ShortComplex C} (hS : ShortExactA S) (Y : C)
    (h₀ : Subsingleton (ExtX₂ S Y 1)) (h₁ : Subsingleton (ExtX₂ S Y 2)) : ExtX₃ S Y 2 ≃+ ExtX₁ S Y 1 :=
  (AddEquiv.ofBijective _ (precomp_extClass_bijective hS Y (show 1 + 1 = 2 from rfl) h₀ h₁)).symm

end ExtIface

section P1

variable (K : Type u) [Field K] {Λ : Type u} [CommRing Λ]

/-- The Mayer-Vietoris short complex of the two standard charts of `P^1` is short exact. -/
theorem P1.seB : ShortExactA (C := EtSh Λ (P1 K))
    (mvS (unitSh Λ (P1 K)) (chartA1 K).opensRange (chartA1' K).opensRange) :=
  mvS_shortExact (P1.cover K)

/-- The middle term of the `P^1` Mayer-Vietoris sequence has no `Ext^n` when `H^n(A^1, Λ) = 0`. -/
theorem P1.subB (n : ℕ) (h : Subsingleton (H Λ (unitSh Λ (A1 K)) n)) :
    Subsingleton (ExtX₂ (C := EtSh Λ (P1 K))
      (mvS (unitSh Λ (P1 K)) (chartA1 K).opensRange (chartA1' K).opensRange) (unitSh Λ (P1 K)) n) :=
  haveI := h
  subsingleton_ext_biprod (cutH (chartA1 K) n).toEquiv.subsingleton (cutH (chartA1' K) n).toEquiv.subsingleton

/-- The `P^1` Mayer-Vietoris equivalence, typed by the generic interface. -/
def P1.e0G (h1 : Subsingleton (H Λ (unitSh Λ (A1 K)) 1)) (h2 : Subsingleton (H Λ (unitSh Λ (A1 K)) 2)) :
    ExtX₃ (C := EtSh Λ (P1 K)) (mvS (unitSh Λ (P1 K)) (chartA1 K).opensRange (chartA1' K).opensRange)
        (unitSh Λ (P1 K)) 2 ≃+
      ExtX₁ (C := EtSh Λ (P1 K)) (mvS (unitSh Λ (P1 K)) (chartA1 K).opensRange (chartA1' K).opensRange)
        (unitSh Λ (P1 K)) 1 :=
  mvEquivGen (P1.seB K) _ (P1.subB K 1 h1) (P1.subB K 2 h2)

end P1

end RamanujanPetersson.EtCompact

end

end


