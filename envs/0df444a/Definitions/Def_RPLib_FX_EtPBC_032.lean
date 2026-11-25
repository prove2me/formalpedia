-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_032
-- name    : RPLib_FX_EtPBC_032
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:29:31.364488+00:00
-- url     : https://prove2.me/theorems/1ebbf487-b4bd-52e3-bed9-8d468571a8fb
-- title:
--   Proper base change for the projective line, library file 032
-- statement:
--   File 032 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2Kmul`: S4-EtPBC-A, O2 M6 (O2Kmul): the Kummer characters `kumD` are multiplicative in the radical
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_027
import Definitions.Def_RPLib_FX_EtPBC_029

/-!
# Proper base change for the projective line, library file 032

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2Kmul`: S4-EtPBC-A, O2 M6 (O2Kmul): the Kummer characters `kumD` are multiplicative in the radical
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_LshEt =====
section

/-!
# S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`

For an etale `e : U ⟶ X`, a geometric point `x` of `X` and a module `J`, the restriction
`res e (x_* J)` of the skyscraper sheaf is assembled from the skyscraper sheaves `l_* J` at the
lifts `l` of `x` along `e` (`pr`, `assemble`, `assemble_pr`, `hom_ext_pr`). Hence:
* `injective_res_sky`: `res e (x_* J)` is injective for `J` injective;
* `res e` preserves injective objects (every injective is a retract of its god sheaf);
* **`lsh e Λ = e_!` preserves monomorphisms** (Mathlib's
  `preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtSheaves.LshEt

universe u

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (x : GeomPt X)

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

/-- **`e_!` preserves monomorphisms for every etale `e`.** -/
instance lsh_preservesMonomorphisms' : (lsh e Λ).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects (lshAdj e Λ)

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

variable (Λ) in
/-- `Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`. -/
def extFreeV (W : P.Etale) (V : W.left.Etale) (F : EtSh Λ P) (n : ℕ) :
    Ext.{u} (freeSh Λ ((etComp W.hom).obj V)) F n ≃+ Ext.{u} (freeSh Λ V) ((res W.hom Λ).obj F) n :=
  (extIsoLeft (lshFreeIso Λ W.hom V).symm F n).trans (extAdjEquiv (lshAdj W.hom Λ) (freeSh Λ V) F n)

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Kmul =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Kmul): the Kummer characters `kumD` are multiplicative in the radical

* `mem_fixUnits_of_pow_eq`: `α ^ d = β ^ d` with `β` Galois-fixed ⇒ `α` Galois-fixed (`α / β` is a power of the
  fixed primitive `d`-th root `ζ ^ (N / d)`);
* **`kumD_mul`**: `kumD (α β) = kumD α + kumD β`; `kumD_of_fix`: `kumD α = 0` for `α` Galois-fixed;
* `kumD_inv`, `kumD_mul_fix` (`β` fixed ⇒ `kumD (α β) = kumD α`);
* **`kumD_congr`**: `kumD α` depends only on `α ^ d`; `kumD_eq_zero_of_pow`: `α ^ d = v ^ d` with `v ∈ K` ⇒
  `kumD α = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Kmul

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {Λ : Type} [AddCommGroup Λ] {N : ℕ} [NeZero N]
  {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)

/-- **`kumD` is additive in the radical.** -/
theorem kumD_mul {α β : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
    (hβ : β ∈ rad (⊤ : Subgroup (Pi1 A K)) d) {g : Λ} (hg : d • g = 0) :
    kumD hζ hζΓ hdN ((rad (⊤ : Subgroup (Pi1 A K)) d).mul_mem hα hβ) hg =
      kumD hζ hζΓ hdN hα hg + kumD hζ hζΓ hdN hβ hg := by
  apply Subtype.ext
  funext σ
  show kumChi (primd hζ hdN) (α * β) g σ = kumChi (primd hζ hdN) α g σ + kumChi (primd hζ hdN) β g σ
  unfold kumChi
  rw [kchar_mul_left (primd hζ hdN) hα hβ, val_add_smul hg]

/-- `kumD α = 0` for a Galois-fixed `α`. -/
theorem kumD_of_fix {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
    (hfix : α ∈ fixUnits (⊤ : Subgroup (Pi1 A K))) {g : Λ} (hg : d • g = 0) :
    kumD hζ hζΓ hdN hα hg = 0 := by
  apply Subtype.ext
  funext σ
  show kumChi (primd hζ hdN) α g σ = 0
  unfold kumChi
  rw [kchar_of_fix (primd hζ hdN) hfix, ZMod.val_zero, zero_smul]

/-- `kumD (α β) = kumD α` for a Galois-fixed `β`. -/
theorem kumD_mul_fix {α β : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d)
    (hβ : β ∈ fixUnits (⊤ : Subgroup (Pi1 A K))) {g : Λ} (hg : d • g = 0) :
    kumD hζ hζΓ hdN ((rad (⊤ : Subgroup (Pi1 A K)) d).mul_mem hα (fixUnits_le_rad _ d hβ)) hg =
      kumD hζ hζΓ hdN hα hg := by
  rw [kumD_mul hζ hζΓ hdN hα (fixUnits_le_rad _ d hβ) hg, kumD_of_fix hζ hζΓ hdN _ hβ, add_zero]

end Kmul

end RamanujanPetersson.EtPBC.EtKum

end

end


