-- Prove2me | Definitions.Def_RPLib_S4_CDPack29b
-- name    : RPLib_S4_CDPack29b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:34:52.522221+00:00
-- url     : https://prove2.me/theorems/228eebdc-e445-4d38-a630-1407a3c1d8f1
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 29b of 71
-- statement:
--   Part 29b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Shrink`: S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`
--   * `Def_RP_JacLaw_ShrinkC`: S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`
--   * `Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
--   * `Def_RP_JacLaw_GeoRed`: S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack29
import Definitions.Def_RPLib_S4_CDPack28c

/-!
# Curve-duality library package, part 29b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Shrink`: S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`
* `Def_RP_JacLaw_ShrinkC`: S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`
* `Def_RP_JacLaw_Law`: S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities
* `Def_RP_JacLaw_GeoRed`: S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Shrink =====
section

/-!
# S4-JacLaw, file O10d-2: from a birational law on a domain `S` to an `AffChunk` on `S[1/u0]`

`PreChunk K S`: `m` on `D(ω)`, `r(a,c)` on `D(ωr)`, `l(c,b)` on `D(ωl)` (opens of `Spec (S ⊗ S)`), the inverse relations
and associativity at `K`-points, and one point of `D(ω)` where `(a, m(a,b)) ∈ D(ωr)` and `(m(a,b), b) ∈ D(ωl)`.
`PreChunk.toAff`: shrink `Spec S` to `D(u0)` so that all fibres of `D(ω') → X` are nonempty.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

/-- Birational group-law data on `S` (see the module doc). -/
structure PreChunk (K S : Type u) [Field K] [CommRing S] [Algebra K S] where
  ω : S ⊗[K] S
  μ : S →ₐ[K] Localization.Away ω
  ωr : S ⊗[K] S
  ρ : S →ₐ[K] Localization.Away ωr
  ωl : S ⊗[K] S
  la : S →ₐ[K] Localization.Away ωl
  r_m : ∀ (x : Localization.Away ω →ₐ[K] K) (x' : Localization.Away ωr →ₐ[K] K),
    pL x' = pL x → pR x' = x.comp μ → x'.comp ρ = pR x
  m_r : ∀ (x' : Localization.Away ωr →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    pL x = pL x' → pR x = x'.comp ρ → x.comp μ = pR x'
  l_m : ∀ (x : Localization.Away ω →ₐ[K] K) (x' : Localization.Away ωl →ₐ[K] K),
    pR x' = pR x → pL x' = x.comp μ → x'.comp la = pL x
  m_l : ∀ (x' : Localization.Away ωl →ₐ[K] K) (x : Localization.Away ω →ₐ[K] K),
    pR x = pR x' → pL x = x'.comp la → x.comp μ = pL x'
  assoc : ∀ x₁ x₂ x₃ x₄ : Localization.Away ω →ₐ[K] K, pR x₁ = pL x₂ → pL x₃ = x₁.comp μ →
    pR x₃ = pR x₂ → pL x₄ = pL x₁ → pR x₄ = x₂.comp μ → x₃.comp μ = x₄.comp μ
  wit : ∃ x : Localization.Away ω →ₐ[K] K, x (phiS μ ωr) ≠ 0 ∧ x (psiS μ ωl) ≠ 0

namespace PreChunk

variable {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S] (P : PreChunk K S)

theorem phi1 (x : Localization.Away P.ω →ₐ[K] K) (h1 : x (phiS P.μ P.ωr) ≠ 0) (s : S) (hs : (pR x) s ≠ 0) :
    x (phiS P.μ (numA (P.ρ s))) ≠ 0 := by
  have z : pair (pL x) (x.comp P.μ) P.ωr ≠ 0 := by rw [← phiS_pt]; exact h1
  obtain ⟨x', hx', hL, hR⟩ := exists_over_pair z
  have h2 : x' (P.ρ s) ≠ 0 := by rw [← AlgHom.comp_apply, P.r_m x x' hL hR]; exact hs
  have h3 := (numA_pt (P.ρ s) x').2 h2
  rw [hx', ← phiS_pt] at h3
  exact h3

theorem psi1 (x : Localization.Away P.ω →ₐ[K] K) (h1 : x (psiS P.μ P.ωl) ≠ 0) (s : S) (hs : (pL x) s ≠ 0) :
    x (psiS P.μ (numA (P.la s))) ≠ 0 := by
  have z : pair (x.comp P.μ) (pR x) P.ωl ≠ 0 := by rw [← psiS_pt]; exact h1
  obtain ⟨x', hx', hL, hR⟩ := exists_over_pair z
  have h2 : x' (P.la s) ≠ 0 := by rw [← AlgHom.comp_apply, P.l_m x x' hR hL]; exact hs
  have h3 := (numA_pt (P.la s) x').2 h2
  rw [hx', ← psiS_pt] at h3
  exact h3

theorem phi3 (x : Localization.Away P.ω →ₐ[K] K) (x' : Localization.Away P.ωr →ₐ[K] K)
    (h : x'.comp (awayι P.ωr) = x.comp (phiS P.μ)) : x'.comp (phiS P.ρ) = x.comp (awayι P.ω) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (phiS_pt P.μ x))
  rw [phiS_pt, base_pair, hL, P.r_m x x' hL hR]

theorem phi4 (x' : Localization.Away P.ωr →ₐ[K] K) (x : Localization.Away P.ω →ₐ[K] K)
    (h : x.comp (awayι P.ω) = x'.comp (phiS P.ρ)) : x.comp (phiS P.μ) = x'.comp (awayι P.ωr) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (phiS_pt P.ρ x'))
  rw [phiS_pt, base_pair, hL, P.m_r x' x hL hR]

theorem psi3 (x : Localization.Away P.ω →ₐ[K] K) (x' : Localization.Away P.ωl →ₐ[K] K)
    (h : x'.comp (awayι P.ωl) = x.comp (psiS P.μ)) : x'.comp (psiS P.la) = x.comp (awayι P.ω) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (psiS_pt P.μ x))
  rw [psiS_pt, base_pair, hR, P.l_m x x' hR hL]

theorem psi4 (x' : Localization.Away P.ωl →ₐ[K] K) (x : Localization.Away P.ω →ₐ[K] K)
    (h : x.comp (awayι P.ω) = x'.comp (psiS P.la)) : x.comp (psiS P.μ) = x'.comp (awayι P.ωl) := by
  obtain ⟨hL, hR⟩ := pts_of_base (h.trans (psiS_pt P.la x'))
  rw [psiS_pt, base_pair, hR, P.m_l x' x hR hL]

/-- `(a, b) ↦ (a, m(a,b)) ∈ D(ωr)`. -/
noncomputable def t1 : S ⊗[K] S := numA (phiS P.μ P.ωr)

/-- `(a, b) ↦ (m(a,b), b) ∈ D(ωl)`. -/
noncomputable def t2 : S ⊗[K] S := numA (psiS P.μ P.ωl)

/-- The witness point. -/
noncomputable def x0 : Localization.Away P.ω →ₐ[K] K := P.wit.choose

/-- `u0(a) = (t1 t2)(a, b0) · (t1 t2)(a0, a)`. -/
noncomputable def u0 : S := slR (pR P.x0) (P.t1 * P.t2) * slL (pL P.x0) (P.t1 * P.t2)

theorem u0_left (a : S →ₐ[K] K) (ha : a P.u0 ≠ 0) : pair a (pR P.x0) (P.t1 * P.t2) ≠ 0 := by
  rw [u0, map_mul] at ha
  have h := left_ne_zero_of_mul ha
  rwa [← AlgHom.comp_apply, slR_pt] at h

theorem u0_right (b : S →ₐ[K] K) (hb : b P.u0 ≠ 0) : pair (pL P.x0) b (P.t1 * P.t2) ≠ 0 := by
  rw [u0, map_mul] at hb
  have h := right_ne_zero_of_mul hb
  rwa [← AlgHom.comp_apply, slL_pt] at h

variable [IsAlgClosed K] [IsDomain S] [Algebra.FiniteType K S]

theorem u0_ne : P.u0 ≠ 0 := by
  have h0 : pair (pL P.x0) (pR P.x0) (P.t1 * P.t2) ≠ 0 := by
    rw [← base_pair, map_mul]
    exact mul_ne_zero ((numA_pt _ _).2 P.wit.choose_spec.1) ((numA_pt _ _).2 P.wit.choose_spec.2)
  refine mul_ne_zero (ne_zero_of_pt (K := K) ⟨pL P.x0, ?_⟩) (ne_zero_of_pt (K := K) ⟨pR P.x0, ?_⟩)
  · rw [← AlgHom.comp_apply, slR_pt]; exact h0
  · rw [← AlgHom.comp_apply, slL_pt]; exact h0

instance isDomain_u0 : IsDomain (Localization.Away P.u0) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors P.u0_ne)

theorem fibL_S (a : S →ₐ[K] K) (ha : a P.u0 ≠ 0) :
    ∃ b : S →ₐ[K] K, b P.u0 ≠ 0 ∧ pair a b (P.t1 * P.t2 * numA (P.μ P.u0)) ≠ 0 := by
  have hF := P.u0_left a ha
  rw [map_mul] at hF
  have h1 : pair a (pR P.x0) P.t1 ≠ 0 := left_ne_zero_of_mul hF
  obtain ⟨x1, hx1, hL1, -⟩ := exists_over_pair (numA_base (phiS P.μ P.ωr) _ h1)
  have hx1r : x1 (phiS P.μ P.ωr) ≠ 0 := (numA_pt (phiS P.μ P.ωr) x1).1 (by rw [hx1]; exact h1)
  have z1 : pair (pL x1) (x1.comp P.μ) P.ωr ≠ 0 := by rw [← phiS_pt]; exact hx1r
  obtain ⟨x1', hx1', hL1', hR1'⟩ := exists_over_pair z1
  have hr1 := P.r_m x1 x1' hL1' hR1'
  have w1 : pair a (x1.comp P.μ) (numA (phiS P.ρ P.ω)) ≠ 0 := by
    rw [← hL1, ← hx1', numA_pt, ← AlgHom.comp_apply, phiS_pt, hL1', hr1, ← base_pair, hx1]
    exact numA_base (phiS P.μ P.ωr) _ h1
  obtain ⟨c, hc1, hc2⟩ := exists_pt_ne2 (K := K) (f := slL a (numA (phiS P.ρ P.ω))) (g := P.u0)
    ⟨x1.comp P.μ, by rw [← AlgHom.comp_apply, slL_pt]; exact w1⟩ ⟨a, ha⟩
  rw [← AlgHom.comp_apply, slL_pt] at hc1
  obtain ⟨x', hx', hL', hR'⟩ := exists_over_pair (numA_base (phiS P.ρ P.ω) _ hc1)
  have hx'w : x' (phiS P.ρ P.ω) ≠ 0 := (numA_pt (phiS P.ρ P.ω) x').1 (by rw [hx']; exact hc1)
  have z2 : pair (pL x') (x'.comp P.ρ) P.ω ≠ 0 := by rw [← phiS_pt]; exact hx'w
  obtain ⟨x2, -, hL2, hR2⟩ := exists_over_pair z2
  have hm2 := P.m_r x' x2 hL2 hR2
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_pt_ne3 (K := K) (f := slL a (P.t1 * P.t2))
    (g := slL a (numA (P.μ P.u0))) (h := P.u0)
    ⟨pR P.x0, by rw [← AlgHom.comp_apply, slL_pt, map_mul]; exact hF⟩
    ⟨x'.comp P.ρ, by
      rw [← AlgHom.comp_apply, slL_pt, ← hL', ← hL2, ← hR2, ← base_pair, numA_pt, ← AlgHom.comp_apply, hm2, hR']
      exact hc2⟩
    ⟨a, ha⟩
  refine ⟨b, hb3, ?_⟩
  rw [← AlgHom.comp_apply, slL_pt] at hb1 hb2
  rw [map_mul]; exact mul_ne_zero hb1 hb2

theorem fibR_S (b : S →ₐ[K] K) (hb : b P.u0 ≠ 0) :
    ∃ a : S →ₐ[K] K, a P.u0 ≠ 0 ∧ pair a b (P.t1 * P.t2 * numA (P.μ P.u0)) ≠ 0 := by
  have hF := P.u0_right b hb
  rw [map_mul] at hF
  have h2 : pair (pL P.x0) b P.t2 ≠ 0 := right_ne_zero_of_mul hF
  obtain ⟨x1, hx1, -, hR1⟩ := exists_over_pair (numA_base (psiS P.μ P.ωl) _ h2)
  have hx1l : x1 (psiS P.μ P.ωl) ≠ 0 := (numA_pt (psiS P.μ P.ωl) x1).1 (by rw [hx1]; exact h2)
  have z1 : pair (x1.comp P.μ) (pR x1) P.ωl ≠ 0 := by rw [← psiS_pt]; exact hx1l
  obtain ⟨x1', hx1', hL1', hR1'⟩ := exists_over_pair z1
  have hl1 := P.l_m x1 x1' hR1' hL1'
  have w1 : pair (x1.comp P.μ) b (numA (psiS P.la P.ω)) ≠ 0 := by
    rw [← hR1, ← hx1', numA_pt, ← AlgHom.comp_apply, psiS_pt, hR1', hl1, ← base_pair, hx1]
    exact numA_base (psiS P.μ P.ωl) _ h2
  obtain ⟨c, hc1, hc2⟩ := exists_pt_ne2 (K := K) (f := slR b (numA (psiS P.la P.ω))) (g := P.u0)
    ⟨x1.comp P.μ, by rw [← AlgHom.comp_apply, slR_pt]; exact w1⟩ ⟨b, hb⟩
  rw [← AlgHom.comp_apply, slR_pt] at hc1
  obtain ⟨x', hx', hL', hR'⟩ := exists_over_pair (numA_base (psiS P.la P.ω) _ hc1)
  have hx'w : x' (psiS P.la P.ω) ≠ 0 := (numA_pt (psiS P.la P.ω) x').1 (by rw [hx']; exact hc1)
  have z2 : pair (x'.comp P.la) (pR x') P.ω ≠ 0 := by rw [← psiS_pt]; exact hx'w
  obtain ⟨x2, -, hL2, hR2⟩ := exists_over_pair z2
  have hm2 := P.m_l x' x2 hR2 hL2
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_pt_ne3 (K := K) (f := slR b (P.t1 * P.t2))
    (g := slR b (numA (P.μ P.u0))) (h := P.u0)
    ⟨pL P.x0, by rw [← AlgHom.comp_apply, slR_pt, map_mul]; exact hF⟩
    ⟨x'.comp P.la, by
      rw [← AlgHom.comp_apply, slR_pt, ← hR', ← hR2, ← hL2, ← base_pair, numA_pt, ← AlgHom.comp_apply, hm2, hL']
      exact hc2⟩
    ⟨b, hb⟩
  refine ⟨a, ha3, ?_⟩
  rw [← AlgHom.comp_apply, slR_pt] at ha1 ha2
  rw [map_mul]; exact mul_ne_zero ha1 ha2

end PreChunk

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_ShrinkC =====
section

/-!
# S4-JacLaw, file O10d-3: the `AffChunk` on `S[1/u0]`

`PreChunk.toAff`: the birational law of a `PreChunk K S`, base-changed to `R = S[1/u0]`, is an `AffChunk K R`
(`ω' = e·num(μ u0)` with `e = t1 t2`, `ωΦ = num(ρ u0)`, `ωΨ = num(λ u0)`); `PreChunk.toStrict'` is its strict chunk.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

namespace PreChunk

variable {K : Type u} [Field K] [IsAlgClosed K] {S : Type u} [CommRing S] [Algebra K S]
  [Algebra.FiniteType K S] (P : PreChunk K S)

theorem t12_left (x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K) :
    (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (phiS P.μ P.ωr) ≠ 0 := by
  have e1 := extK_e P.u0 (P.t1 * P.t2) P.μ x
  rw [map_mul] at e1
  exact (numA_pt (phiS P.μ P.ωr) _).1 (left_ne_zero_of_mul e1)

theorem t12_right (x : Localization.Away (extW P.u0 (P.t1 * P.t2) P.μ) →ₐ[K] K) :
    (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (psiS P.μ P.ωl) ≠ 0 := by
  have e1 := extK_e P.u0 (P.t1 * P.t2) P.μ x
  rw [map_mul] at e1
  exact (numA_pt (psiS P.μ P.ωl) _).1 (right_ne_zero_of_mul e1)

variable [IsDomain S]

/-- The algebraic chunk data on `S[1/u0]`. -/
noncomputable def toAff : AffChunk K (Localization.Away P.u0) where
  ω := extW P.u0 (P.t1 * P.t2) P.μ
  μ := extN P.u0 (P.t1 * P.t2) P.μ
  ωΦ := extW P.u0 1 P.ρ
  gΦ := phiS (extN P.u0 1 P.ρ)
  Φ1 x := by
    have e : x (phiS (extN P.u0 (P.t1 * P.t2) P.μ) (extW P.u0 1 P.ρ)) =
        (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (phiS P.μ (numA (P.ρ P.u0))) := by
      change x (((phiS (extN P.u0 (P.t1 * P.t2) P.μ)).comp (jj K P.u0)) (1 * numA (P.ρ P.u0))) = _
      rw [phiS_ext, one_mul]; rfl
    rw [e]
    exact P.phi1 _ (P.t12_left x) P.u0 (extK_uR P.u0 (P.t1 * P.t2) P.μ x)
  Φ3 x y h := by
    refine jj_ext P.u0 ?_
    rw [← extK_phi P.u0 1 P.ρ y, ← extK_base P.u0 (P.t1 * P.t2) P.μ x]
    exact P.phi3 _ _ (by rw [extK_base P.u0 1 P.ρ y, h, extK_phi P.u0 (P.t1 * P.t2) P.μ x])
  Φ4 y x h := by
    refine jj_ext P.u0 ?_
    rw [← extK_phi P.u0 (P.t1 * P.t2) P.μ x, ← extK_base P.u0 1 P.ρ y]
    exact P.phi4 _ _ (by rw [extK_base P.u0 (P.t1 * P.t2) P.μ x, h, extK_phi P.u0 1 P.ρ y])
  ωΨ := extW P.u0 1 P.la
  gΨ := psiS (extN P.u0 1 P.la)
  Ψ1 x := by
    have e : x (psiS (extN P.u0 (P.t1 * P.t2) P.μ) (extW P.u0 1 P.la)) =
        (x.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (psiS P.μ (numA (P.la P.u0))) := by
      change x (((psiS (extN P.u0 (P.t1 * P.t2) P.μ)).comp (jj K P.u0)) (1 * numA (P.la P.u0))) = _
      rw [psiS_ext, one_mul]; rfl
    rw [e]
    exact P.psi1 _ (P.t12_right x) P.u0 (extK_uL P.u0 (P.t1 * P.t2) P.μ x)
  Ψ3 x y h := by
    refine jj_ext P.u0 ?_
    rw [← extK_psi P.u0 1 P.la y, ← extK_base P.u0 (P.t1 * P.t2) P.μ x]
    exact P.psi3 _ _ (by rw [extK_base P.u0 1 P.la y, h, extK_psi P.u0 (P.t1 * P.t2) P.μ x])
  Ψ4 y x h := by
    refine jj_ext P.u0 ?_
    rw [← extK_psi P.u0 (P.t1 * P.t2) P.μ x, ← extK_base P.u0 1 P.la y]
    exact P.psi4 _ _ (by rw [extK_base P.u0 (P.t1 * P.t2) P.μ x, h, extK_psi P.u0 1 P.la y])
  fibL a := by
    have ha : (a.comp (awayι P.u0)) P.u0 ≠ 0 := baseAway_ne P.u0 a
    obtain ⟨b, hb, hab⟩ := P.fibL_S _ ha
    obtain ⟨y, hy, -⟩ := exists_ext_pt P.u0 (P.t1 * P.t2) P.μ _ b ha hb hab
    exact ⟨y, away_algHom_ext hy⟩
  fibR b := by
    have hb : (b.comp (awayι P.u0)) P.u0 ≠ 0 := baseAway_ne P.u0 b
    obtain ⟨a, ha, hab⟩ := P.fibR_S _ hb
    obtain ⟨y, -, hy⟩ := exists_ext_pt P.u0 (P.t1 * P.t2) P.μ a _ ha hb hab
    exact ⟨y, away_algHom_ext hy⟩
  assoc x₁ x₂ x₃ x₄ e₁ e₂ e₃ e₄ e₅ := by
    refine away_algHom_ext ?_
    rw [← extK_nu P.u0 (P.t1 * P.t2) P.μ x₃, ← extK_nu P.u0 (P.t1 * P.t2) P.μ x₄]
    refine P.assoc (x₁.comp (extK P.u0 (P.t1 * P.t2) P.μ)) (x₂.comp (extK P.u0 (P.t1 * P.t2) P.μ)) _ _
      ?_ ?_ ?_ ?_ ?_
    · rw [extK_pR, extK_pL, e₁]
    · rw [extK_pL, e₂, extK_nu]
    · rw [extK_pR, extK_pR, e₃]
    · rw [extK_pL, extK_pL, e₄]
    · rw [extK_pR, e₅, extK_nu]

/-- The strict group chunk on `Spec S[1/u0]` defined by a `PreChunk`. -/
noncomputable def toStrict' : StrictChunk (k := K) (sR K (Localization.Away P.u0)) := P.toAff.toStrict

end PreChunk

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Law =====
section

/-!
# S4-JacLaw, file O8c: the law maps `m`, `r` and the inverse identities

* `eq_of_ptSet_eq`: reduced points of `Sym^n` with the same support are equal.
* `back_mr`, `back_rm` (supports, two swap steps each): `r(a, m(a,b)) = b` and `m(a, r(a,c)) = c`.
* Generic source `T` (reduced, f.g.): `mOut D3 D2 c0 c1 φa φb : Sym^g → T[1/u3][1/u2]` with points
  `ν2(ν3(a + b + c0) + c1)`, and `rOut D3 D2 c0 c1 φa φc` with points `ν3(a + ν2(c + c1) + c0)` (the inverse
  `l(c,b)` of the other translation is `rOut` with `φa := φb` and its own data); point lemmas `pts_mOut`, `pts_rOut`.
* Composite identities at points: `r_mOut`, `l_mOut`, `m_rOut`, `m_lOut`.
* `LawData K F`: padding tuples and six choice data (roles m, r, l at levels 3 and 2, same `Hn` per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

open Classical in
theorem eq_of_ptSet_eq {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}
    {y y' : SymRing k B n →ₐ[k] k} (h : ptSet y = ptSet y') (hc : (ptSet y).card = n) : y = y' := by
  have hi : ∀ z : SymRing k B n →ₐ[k] k, (ptSet z).card = n → Function.Injective (liftTuple z) := by
    intro z hz i j hij
    have h1 : (Finset.univ.image (liftTuple z)).card = (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact hz
    exact Finset.card_image_iff.1 h1 (Finset.mem_coe.2 (Finset.mem_univ i))
      (Finset.mem_coe.2 (Finset.mem_univ j)) hij
  have e := symPt_eq_of_image_eq (hi y hc) (hi y' (h ▸ hc)) h
  rwa [symPt_liftTuple, symPt_liftTuple] at e

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

open Classical in
/-- `r(a, m(a,b)) = b` on supports: `y3 = A ⊔ B ⊔ C0`, `y2 = ν3(y3) ∪ C1`, `y2' = ν2(y2) ∪ C1`,
`y3' = A ∪ ν2'(y2') ∪ C0` ⇒ `ν3'(y3') = B`. -/
theorem back_mr {d3 d2 r3 r2 : ℕ} (hd3 : d3 = genusFK K F + genusFK K F + r3) (hd2 : d2 = genusFK K F + r2)
    {D3 D3' : NuData K F d3} {D2 D2' : NuData K F d2} (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn)
    {y3 y3' : SymRing K (Places.Rfin K F) d3 →ₐ[K] K} {y2 y2' : SymRing K (Places.Rfin K F) d2 →ₐ[K] K}
    (hy3 : y3 D3.good ≠ 0) (hy2 : y2 D2.good ≠ 0) (hy2' : y2' D2'.good ≠ 0) (hy3' : y3' D3'.good ≠ 0)
    {A Bs C0 C1 : Finset (Places.Rfin K F →ₐ[K] K)} (hA : A.card ≤ genusFK K F) (hB : Bs.card ≤ genusFK K F)
    (hC0 : C0.card ≤ r3) (hC1 : C1.card ≤ r2) (e3 : ptSet y3 = A ∪ Bs ∪ C0) (e2 : ptSet y2 = D3.nuF y3 ∪ C1)
    (e2' : ptSet y2' = D2.nuF y2 ∪ C1) (e3' : ptSet y3' = A ∪ D2'.nuF y2' ∪ C0) : D3'.nuF y3' = Bs := by
  have hE := card_nuF hy3
  obtain ⟨hdE, -, -⟩ := disjoint_of_card_union hE.le hC1 (by rw [← e2, card_ptSet hy2, hd2])
  have s1 : D2'.nuF y2' = D3.nuF y3 :=
    swap_step (P := C1) (Q := D3.nuF y3) (by omega) h2 hy2 hy2' (by rw [e2, Finset.union_comm]) hdE.symm
      (by rw [e2', Finset.union_comm])
  have hAB : (A ∪ Bs).card ≤ genusFK K F + genusFK K F := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨hABC, hABc, -⟩ := disjoint_of_card_union hAB hC0 (by rw [← e3, card_ptSet hy3, hd3])
  obtain ⟨hAB', -, -⟩ := disjoint_of_card_union hA hB hABc
  exact swap_step (P := A ∪ C0) (Q := Bs) (by omega) h3 hy3 hy3' (by rw [e3, Finset.union_right_comm])
    (Finset.disjoint_union_left.2 ⟨hAB', (Finset.disjoint_union_left.1 hABC).2.symm⟩)
    (by rw [e3', s1, Finset.union_right_comm])

open Classical in
/-- `m(a, r(a,c)) = c` on supports: `y2 = C ⊔ C1`, `y3 = A ∪ ν2(y2) ∪ C0`, `y3' = A ∪ ν3(y3) ∪ C0`,
`y2' = ν3'(y3') ∪ C1` ⇒ `ν2'(y2') = C`. -/
theorem back_rm {d3 d2 r3 r2 : ℕ} (hd3 : d3 = genusFK K F + genusFK K F + r3) (hd2 : d2 = genusFK K F + r2)
    {D3 D3' : NuData K F d3} {D2 D2' : NuData K F d2} (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn)
    {y3 y3' : SymRing K (Places.Rfin K F) d3 →ₐ[K] K} {y2 y2' : SymRing K (Places.Rfin K F) d2 →ₐ[K] K}
    (hy2 : y2 D2.good ≠ 0) (hy3 : y3 D3.good ≠ 0) (hy3' : y3' D3'.good ≠ 0) (hy2' : y2' D2'.good ≠ 0)
    {A Cs C0 C1 : Finset (Places.Rfin K F →ₐ[K] K)} (hA : A.card ≤ genusFK K F) (hC : Cs.card ≤ genusFK K F)
    (hC0 : C0.card ≤ r3) (hC1 : C1.card ≤ r2) (e2 : ptSet y2 = Cs ∪ C1) (e3 : ptSet y3 = A ∪ D2.nuF y2 ∪ C0)
    (e3' : ptSet y3' = A ∪ D3.nuF y3 ∪ C0) (e2' : ptSet y2' = D3'.nuF y3' ∪ C1) : D2'.nuF y2' = Cs := by
  have hE := card_nuF hy2
  have hAE : (A ∪ D2.nuF y2).card ≤ genusFK K F + genusFK K F := (Finset.card_union_le _ _).trans (by omega)
  obtain ⟨hAEC, hAEc, -⟩ := disjoint_of_card_union hAE hC0 (by rw [← e3, card_ptSet hy3, hd3])
  obtain ⟨hAE', -, -⟩ := disjoint_of_card_union hA hE.le hAEc
  have s1 : D3'.nuF y3' = D2.nuF y2 :=
    swap_step (P := A ∪ C0) (Q := D2.nuF y2) (by omega) h3 hy3 hy3' (by rw [e3, Finset.union_right_comm])
      (Finset.disjoint_union_left.2 ⟨hAE', (Finset.disjoint_union_left.1 hAEC).2.symm⟩)
      (by rw [e3', Finset.union_right_comm])
  obtain ⟨hdC, -, -⟩ := disjoint_of_card_union hC hC1 (by rw [← e2, card_ptSet hy2, hd2])
  exact swap_step (P := C1) (Q := Cs) (by omega) h2 hy2 hy2' (by rw [e2, Finset.union_comm]) hdC.symm
    (by rw [e2', s1, Finset.union_comm])

end NuData

section Maps

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

/-- Inner step of `m`: `ν3(a + b + c0)` on `T[1/u3]`. -/
noncomputable def mIn {r3 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (padMap (sumMap φa φb) c0 rfl D3.good) :=
  D3.nuStep (padMap (sumMap φa φb) c0 rfl)

/-- **The law** `m(a,b) = ν2(ν3(a + b + c0) + c1)` on `T[1/u3][1/u2]`. -/
noncomputable def mOut {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K]
      Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) :=
  D2.nuStep (padMap (mIn D3 c0 φa φb) c1 rfl)

/-- The point of `T` below a point of the target of `mOut`. -/
noncomputable def mBase {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) : T →ₐ[K] K :=
  baseAway _ (baseAway _ x)

/-- Inner step of `r`: `ν2(c + c1)` on `T[1/v2]`. -/
noncomputable def rIn {r2 : ℕ} (D2 : NuData K F (genusFK K F + r2)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))
    (φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] Localization.Away (padMap φc c1 rfl D2.good) :=
  D2.nuStep (padMap φc c1 rfl)

/-- The point `a + ν2(c + c1)` of `Sym^(g+g)` over `T[1/v2]`. -/
noncomputable def rSum {r2 : ℕ} (D2 : NuData K F (genusFK K F + r2)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))
    (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F) →ₐ[K] Localization.Away (padMap φc c1 rfl D2.good) :=
  sumMap ((IsScalarTower.toAlgHom K T _).comp φa) (rIn D2 c1 φc)

/-- **The inverse law** `r(a,c) = ν3(a + ν2(c + c1) + c0)` on `T[1/v2][1/v3]`. -/
noncomputable def rOut {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T) :
    SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K]
      Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) :=
  D3.nuStep (padMap (rSum D2 c1 φa φc) c0 rfl)

/-- The point of `T` below a point of the target of `rOut`. -/
noncomputable def rBase {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3))
    (D2 : NuData K F (genusFK K F + r2)) (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K))
    (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)) (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) →ₐ[K] K) : T →ₐ[K] K :=
  baseAway _ (baseAway _ x)

variable {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

open Classical in
theorem pts_mOut (φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K) :
    ∃ (y3 : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K)
      (y2 : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K), y3 D3.good ≠ 0 ∧ y2 D2.good ≠ 0 ∧
      ptSet y3 = ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa) ∪ ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φb) ∪
        Finset.univ.image c0 ∧
      ptSet y2 = D3.nuF y3 ∪ Finset.univ.image c1 ∧
      ptSet (x.comp (mOut D3 D2 c0 c1 φa φb)) = D2.nuF y2 := by
  refine ⟨(baseAway _ (baseAway _ x)).comp (padMap (sumMap φa φb) c0 rfl),
    (baseAway _ x).comp (padMap (mIn D3 c0 φa φb) c1 rfl),
    D3.good_base (padMap (sumMap φa φb) c0 rfl) (baseAway _ x),
    D2.good_base (padMap (mIn D3 c0 φa φb) c1 rfl) x, ?_, ?_,
    D2.ptSet_nuStep (padMap (mIn D3 c0 φa φb) c1 rfl) x⟩
  · rw [comp_padMap, ptSet_padPt, comp_sumMap, ptSet_sumPt]
    rfl
  · rw [comp_padMap, ptSet_padPt]
    exact congrArg (· ∪ Finset.univ.image c1) (D3.ptSet_nuStep (padMap (sumMap φa φb) c0 rfl) (baseAway _ x))

open Classical in
theorem pts_rOut (φa φc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T)
    (x : Localization.Away (padMap (rSum D2 c1 φa φc) c0 rfl D3.good) →ₐ[K] K) :
    ∃ (y2 : SymRing K (Places.Rfin K F) (genusFK K F + r2) →ₐ[K] K)
      (y3 : SymRing K (Places.Rfin K F) (genusFK K F + genusFK K F + r3) →ₐ[K] K), y2 D2.good ≠ 0 ∧
      y3 D3.good ≠ 0 ∧ ptSet y2 = ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φc) ∪ Finset.univ.image c1 ∧
      ptSet y3 = ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φa) ∪ D2.nuF y2 ∪ Finset.univ.image c0 ∧
      ptSet (x.comp (rOut D3 D2 c0 c1 φa φc)) = D3.nuF y3 := by
  refine ⟨(baseAway _ (baseAway _ x)).comp (padMap φc c1 rfl),
    (baseAway _ x).comp (padMap (rSum D2 c1 φa φc) c0 rfl),
    D2.good_base (padMap φc c1 rfl) (baseAway _ x),
    D3.good_base (padMap (rSum D2 c1 φa φc) c0 rfl) x, ?_, ?_,
    D3.ptSet_nuStep (padMap (rSum D2 c1 φa φc) c0 rfl) x⟩
  · rw [comp_padMap, ptSet_padPt]
    rfl
  · rw [comp_padMap, ptSet_padPt]
    show ptSet ((baseAway _ x).comp (sumMap ((IsScalarTower.toAlgHom K T
      (Localization.Away (padMap φc c1 rfl D2.good))).comp φa) (rIn D2 c1 φc))) ∪ Finset.univ.image c0 = _
    rw [comp_sumMap, ptSet_sumPt]
    exact congrArg (fun s => ptSet ((rBase D3 D2 c0 c1 φa φc x).comp φa) ∪ s ∪ Finset.univ.image c0)
      (D2.ptSet_nuStep (padMap φc c1 rfl) (baseAway _ x))

end Maps

section Comp

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {T' : Type*} [CommRing T'] [Algebra K T'] [IsReduced T'] [Algebra.FiniteType K T']
  {r3 r2 : ℕ} {D3 D3' : NuData K F (genusFK K F + genusFK K F + r3)} {D2 D2' : NuData K F (genusFK K F + r2)}
  {c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)} {c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)}

theorem card_image_tuple {r : ℕ} (c : Fin r → (Places.Rfin K F →ₐ[K] K)) [DecidableEq (Places.Rfin K F →ₐ[K] K)] :
    (Finset.univ.image c).card ≤ r :=
  Finset.card_image_le.trans_eq (by simp)

/-- `r(a, m(a,b)) = b` at points (`D3', D2'` the `r` data). -/
theorem r_mOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {ψa ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x' : Localization.Away (padMap (rSum D2' c1 ψa ψc) c0 rfl D3'.good) →ₐ[K] K)
    (ha : (rBase D3' D2' c0 c1 ψa ψc x').comp ψa = (mBase D3 D2 c0 c1 φa φb x).comp φa)
    (hc : (rBase D3' D2' c0 c1 ψa ψc x').comp ψc = x.comp (mOut D3 D2 c0 c1 φa φb)) :
    x'.comp (rOut D3' D2' c0 c1 ψa ψc) = (mBase D3 D2 c0 c1 φa φb x).comp φb := by
  classical
  obtain ⟨y3, y2, hy3, hy2, e3, e2, em⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  obtain ⟨y2', y3', hy2', hy3', e2', e3', er⟩ := pts_rOut D3' D2' c0 c1 ψa ψc x'
  rw [ha] at e3'
  rw [hc, em] at e2'
  have key := NuData.back_mr rfl rfl h3 h2 hy3 hy2 hy2' hy3' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e3 e2 e2' e3'
  exact eq_of_ptSet_eq (by rw [er, key]) (by rw [er, NuData.card_nuF hy3'])

/-- `l(m(a,b), b) = a` at points (`l(c,b) = rOut` with first argument `b`; `D3', D2'` the `l` data). -/
theorem l_mOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {ψb ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x : Localization.Away (padMap (mIn D3 c0 φa φb) c1 rfl D2.good) →ₐ[K] K)
    (x' : Localization.Away (padMap (rSum D2' c1 ψb ψc) c0 rfl D3'.good) →ₐ[K] K)
    (hb : (rBase D3' D2' c0 c1 ψb ψc x').comp ψb = (mBase D3 D2 c0 c1 φa φb x).comp φb)
    (hc : (rBase D3' D2' c0 c1 ψb ψc x').comp ψc = x.comp (mOut D3 D2 c0 c1 φa φb)) :
    x'.comp (rOut D3' D2' c0 c1 ψb ψc) = (mBase D3 D2 c0 c1 φa φb x).comp φa := by
  classical
  obtain ⟨y3, y2, hy3, hy2, e3, e2, em⟩ := pts_mOut D3 D2 c0 c1 φa φb x
  obtain ⟨y2', y3', hy2', hy3', e2', e3', er⟩ := pts_rOut D3' D2' c0 c1 ψb ψc x'
  rw [hb] at e3'
  rw [hc, em] at e2'
  rw [Finset.union_comm (ptSet ((mBase D3 D2 c0 c1 φa φb x).comp φa))] at e3
  have key := NuData.back_mr rfl rfl h3 h2 hy3 hy2 hy2' hy3' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e3 e2 e2' e3'
  exact eq_of_ptSet_eq (by rw [er, key]) (by rw [er, NuData.card_nuF hy3'])

/-- `m(a, r(a,c)) = c` at points (`D3, D2` the `r` data, `D3', D2'` the `m` data). -/
theorem m_rOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {ψa ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x' : Localization.Away (padMap (rSum D2 c1 ψa ψc) c0 rfl D3.good) →ₐ[K] K)
    (x : Localization.Away (padMap (mIn D3' c0 φa φb) c1 rfl D2'.good) →ₐ[K] K)
    (ha : (mBase D3' D2' c0 c1 φa φb x).comp φa = (rBase D3 D2 c0 c1 ψa ψc x').comp ψa)
    (hb : (mBase D3' D2' c0 c1 φa φb x).comp φb = x'.comp (rOut D3 D2 c0 c1 ψa ψc)) :
    x.comp (mOut D3' D2' c0 c1 φa φb) = (rBase D3 D2 c0 c1 ψa ψc x').comp ψc := by
  classical
  obtain ⟨y2, y3, hy2, hy3, e2, e3, er⟩ := pts_rOut D3 D2 c0 c1 ψa ψc x'
  obtain ⟨y3', y2', hy3', hy2', e3', e2', em⟩ := pts_mOut D3' D2' c0 c1 φa φb x
  rw [ha, hb, er] at e3'
  have key := NuData.back_rm rfl rfl h3 h2 hy2 hy3 hy3' hy2' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e2 e3 e3' e2'
  exact eq_of_ptSet_eq (by rw [em, key]) (by rw [em, NuData.card_nuF hy2'])

/-- `m(l(c,b), b) = c` at points (`D3, D2` the `l` data, `D3', D2'` the `m` data). -/
theorem m_lOut (h3 : D3'.Hn = D3.Hn) (h2 : D2'.Hn = D2.Hn) {ψb ψc : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T}
    {φa φb : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] T'}
    (x' : Localization.Away (padMap (rSum D2 c1 ψb ψc) c0 rfl D3.good) →ₐ[K] K)
    (x : Localization.Away (padMap (mIn D3' c0 φa φb) c1 rfl D2'.good) →ₐ[K] K)
    (ha : (mBase D3' D2' c0 c1 φa φb x).comp φa = x'.comp (rOut D3 D2 c0 c1 ψb ψc))
    (hb : (mBase D3' D2' c0 c1 φa φb x).comp φb = (rBase D3 D2 c0 c1 ψb ψc x').comp ψb) :
    x.comp (mOut D3' D2' c0 c1 φa φb) = (rBase D3 D2 c0 c1 ψb ψc x').comp ψc := by
  classical
  obtain ⟨y2, y3, hy2, hy3, e2, e3, er⟩ := pts_rOut D3 D2 c0 c1 ψb ψc x'
  obtain ⟨y3', y2', hy3', hy2', e3', e2', em⟩ := pts_mOut D3' D2' c0 c1 φa φb x
  rw [ha, hb, er, Finset.union_comm (D3.nuF y3)] at e3'
  have key := NuData.back_rm rfl rfl h3 h2 hy2 hy3 hy3' hy2' (card_ptSet_le _) (card_ptSet_le _)
    (card_image_tuple c0) (card_image_tuple c1) e2 e3 e3' e2'
  exact eq_of_ptSet_eq (by rw [em, key]) (by rw [em, NuData.card_nuF hy2'])

end Comp

variable (K F) in
/-- Data of the birational law: padding tuples `c0, c1` and six choice data (roles m, r, l; levels 3 and 2). -/
structure LawData where
  r3 : ℕ
  r2 : ℕ
  c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)
  c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K)
  Dm3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dr3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dl3 : NuData K F (genusFK K F + genusFK K F + r3)
  Dm2 : NuData K F (genusFK K F + r2)
  Dr2 : NuData K F (genusFK K F + r2)
  Dl2 : NuData K F (genusFK K F + r2)
  hr3 : Dr3.Hn = Dm3.Hn
  hl3 : Dl3.Hn = Dm3.Hn
  hr2 : Dr2.Hn = Dm2.Hn
  hl2 : Dl2.Hn = Dm2.Hn

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_GeoRed =====
section

/-!
# S4-JacLaw, file O10c: `Spec R` is geometrically reduced over `K`

For `K` algebraically closed and `R` a finitely generated `K`-domain, `R ⊗[K] L` is a domain for every field `L`
(`isDomain_tensor`), so every base change of `sR K R` to a field is reduced (`geometricallyReduced_sR`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open CategoryTheory Limits AlgebraicGeometry RamanujanPetersson.JacSym
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {R : Type u} [CommRing R] [IsDomain R] [Algebra K R]
  [Algebra.FiniteType K R]

/-- `Spec R` is geometrically reduced over `K`. -/
instance geometricallyReduced_sR : GeometricallyReduced (sR K R) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing]
  intro L _ _ Y fst snd h
  have : IsDomain (R ⊗[K] L) := isDomain_tensor (k := K) (B := R) (A := L)
  exact ObjectProperty.prop_of_iso _ (h.isoPullback ≪≫ pullbackSpecIso K R L).symm inferInstance

end RamanujanPetersson.JacLaw

end


