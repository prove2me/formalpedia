-- Prove2me | Definitions.Def_RPLib_FX_EtP1_10
-- name    : RPLib_FX_EtP1_10
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:13:02.215802+00:00
-- url     : https://prove2.me/theorems/394e560d-db47-5844-94d4-c6a06006a9ec
-- title:
--   Étale cohomology of the projective line, library file 10 of 34
-- statement:
--   File 10 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
--   * `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_09

/-!
# Étale cohomology of the projective line, library file 10 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
* `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_H1 =====
section

/-!
# S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`

* `isRepExt_fibRep`: the generic stalk of `0 → G → P → Λ_X → 0` (`G`, `P` lisse) is an extension of
  `π₁`-representations;
* **`exists_kappa_eq`**: `κ` is surjective (write `e` as the class of a short exact sequence, its middle term is lisse
  by `isLisse_of_ext`, its generic stalk gives the cocycle);
* `kappaZ : Z¹ →+ H¹`, with kernel the coboundaries;
* **`h1Equiv A K hG : H Λ G 1 ≃+ CurveCoh.H1 (fibRep G) ⊤`**, with `h1Equiv_symm_mk`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

section Z1

variable {A K} {G : EtSh Λ (Spec (CommRingCat.of A))} {hG : IsLisse Λ G}

end Z1

variable {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)

/-- **`H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)`** for lisse `G`. -/
def h1Equiv : H Λ G 1 ≃+ CurveCoh.H1 (EssSurj.fibRep A K G hG) ⊤ :=
  (AddEquiv.ofBijective (h1ToH A K hG) (h1ToH_bijective A K hG)).symm

theorem h1Equiv_symm_mk (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) :
    (h1Equiv A K hG).symm (CurveCoh.H1.mk (EssSurj.fibRep A K G hG) ⊤ z) = kappaZ A K hG z := rfl

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1Kum =====
section

/-!
# S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)

`A = k[X]`, `K = Frac A`, `K_U = maxUnram A K`, `π₁ = Pi1 A K`, `N` invertible in `k`.

* `dvd_ord_of_unram0`: for a UFD `R` and `L ∈ unramSet R K`, an `N`-th root `α ∈ L` of `a ∈ Kˣ` forces
  `N ∣ ord_π(den a) - ord_π(num a)` at every prime `π` (level-`0` form of `EtPi1.dvd_ord_of_unram`).
* `fixed_of_pow_fixed`: if `α ∈ K_U` and `α ^ N ∈ K`, then `α ∈ K` (units of `k[X]` are `N`-th powers, roots of unity
  lie in `k`).
* `hom_eq_zero_A1`, `hom_eq_zero_A1_tors`: every locally constant homomorphism `π₁ → V`, `N • V = 0`, vanishes
  (Kummer: `exists_kchar_eq`; finite image + characters).
* **`A1.subsingleton_h1`**: `H^1(A^1_k, Λ) = 0` when `N • Λ = 0`, `(N : k) ≠ 0` (`h1Equiv`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Ord0

variable {R K : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

end Ord0

section Kum

variable {k : Type} [Field k] [IsAlgClosed k] {K : Type} [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

end Kum

section H1

variable (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

/-- **`H^1(A^1_k, Λ) = 0`** for `k` algebraically closed and `N • Λ = 0` with `N` invertible in `k`. -/
theorem A1.subsingleton_h1 {Λ : Type} [CommRing Λ] {N : ℕ} (hN : (N : k) ≠ 0) (hΛ : (N : Λ) = 0) :
    Subsingleton (H Λ (unitSh Λ (Spec (CommRingCat.of k[X]))) 1) := by
  haveI : NeZero N := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  haveI := curveH1_unitSh_subsingleton k (RatFunc k) hN hΛ
  exact (h1Equiv k[X] (RatFunc k) (isLisse_unitSh (Λ := Λ) (X := Spec (CommRingCat.of k[X])))).toEquiv.subsingleton

end H1

end RamanujanPetersson.EtCompact

end

end


