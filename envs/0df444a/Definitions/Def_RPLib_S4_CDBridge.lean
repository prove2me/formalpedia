-- Prove2me | Definitions.Def_RPLib_S4_CDBridge
-- name    : RPLib_S4_CDBridge
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:16:18.606213+00:00
-- url     : https://prove2.me/theorems/6053fe05-3a9b-46e4-9d61-11afa1188e26
-- title:
--   Curve-duality library: the duality theorem on cochains
-- statement:
--   Let $G$ be a topological group, $\Gamma \le G$ a subgroup, $S$ a finite nonempty set, $(I_s)_{s\in S}$ subgroups of $G$, $\Lambda$ a commutative ring and $\sigma$ a $\Lambda$-linear action of $G$ on $\Lambda$ that is trivial on $\Gamma$. A *compactly supported $1$-cocycle* is a pair $x=(c,b)$ with $c:\Gamma\to\Lambda$ a locally constant homomorphism vanishing on every $\Gamma\cap I_s$ and $b:S\to\Lambda$; a *$1$-cocycle* is a locally constant homomorphism $d:\Gamma\to\Lambda$. Given the constant-coefficient data of the curve-duality library (elements $t_s\in\Gamma\cap I_s$, a cup-product hypothesis and the residue data), the class pairing $\langle\cdot,\cdot\rangle : H^1_c(\Gamma,\Lambda)\times H^1(\Gamma,\Lambda(\sigma))\to\Lambda$ is lifted to cochains by
--   $$\langle x,d\rangle=\langle [x],[d]\rangle \ \text{ if $x$ and $d$ are cocycles},\qquad \langle x,d\rangle=0\ \text{ otherwise}.$$
--   This package proves, for this cochain pairing: every cup product $c\cup d$ of homomorphisms is a coboundary $c(g)d(h)=u(h)-u(gh)+u(g)$ of a locally constant $u$; the explicit formula
--   $$\langle (c,b),d\rangle=\sum_{s\in S}\bigl(b_s\,d(t_s)-u(t_s)\bigr)$$
--   for every such $u$; and, when the class pairing is perfect, that its left kernel consists of the pairs $(0,\text{const})$, its right kernel is $0$, every additive $\Lambda$-homogeneous functional on either side (vanishing on the pairs $(0,\text{const})$ for the compact side) is represented by the other side, and that it is multiplied by a given scalar $c_0$ under the Frobenius twists $c'(g)=c(\varphi g\varphi^{-1})$, $d'(g)=\sigma(\varphi^{-1})\,d(\varphi g\varphi^{-1})$, $b'_s=b_{\tau(s)}-c(\eta_s)$ whenever the class pairing has that property.
--
--   These statements are the elementary, cochain-level form of Poincaré duality for constant coefficients on an affine curve over a finite field.
--
--   **Formalization note.** Namespace `RamanujanPetersson.CDBridge`; imports parts 2, 3 and 5 of the curve-duality library and the public files `Def_RPLib_S4_GalCover`, `Def_RPLib_S4_CurveCohCurve` and `Def_RPLib_S4_CurveCohPair`. It also contains three helper equivalences (`unram_iff`, `under_iff`, `mem_smul_iff`) that restate the library's notions of unramified subextension, restriction of a place and Galois action on ideals in explicit terms. All proofs are complete (no `sorry`).
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_GalCover
import Definitions.Def_RPLib_S4_CurveCohCurve
import Definitions.Def_RPLib_S4_CurveCohPair
import Definitions.Def_RPLib_S4_CDPack02
import Definitions.Def_RPLib_S4_CDPack03
import Definitions.Def_RPLib_S4_CDPack05

/-!
# Curve-duality library: the duality theorem on cochains

Companion of the curve-duality library (parts 1-71), whose main result is
`RamanujanPetersson.CupDuality.constDuality_S3_perfect`; it only needs the cohomological core (parts 2, 3 and 5 and
the public files `Def_RPLib_S4_GalCover`, `Def_RPLib_S4_CurveCohCurve`, `Def_RPLib_S4_CurveCohPair`). For a topological group `G`, a subgroup `Γ`, subgroups
`I s` (`s ∈ S`, `S` finite) and constant-coefficient data `DD` for a character `σ : G → Aut_Λ(Λ)` trivial on `Γ`,
this file defines the cup pairing on cochains `cpair` (the pairing of the cohomology classes of a compactly
supported 1-cocycle and a 1-cocycle, `0` off cocycles) and proves, in elementary cochain terms, the explicit formula
for it, its left and right nondegeneracy, that it identifies each side with the dual of the other, and its
compatibility with Frobenius twists. The helpers `unram_iff`, `under_iff` and `mem_smul_iff` restate the library's
predicates (unramified subextension, restriction of a place, Galois action on ideals) explicitly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CDBridge

open scoped Pointwise

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem under_iff {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K]
    [IsFractionRing A K] {M L : IntermediateField K (AlgebraicClosure K)} (h : M ≤ L)
    [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (w : IsDedekindDomain.HeightOneSpectrum (integralClosure A L)) (x : integralClosure A M) :
    x ∈ (CdOne.underI A h w).asIdeal ↔
      ∃ y ∈ w.asIdeal, ((y : L) : AlgebraicClosure K) = ((x : M) : AlgebraicClosure K) := by
  show x ∈ w.asIdeal.comap (incl A K h) ↔ _
  rw [Ideal.mem_comap]
  constructor
  · intro hx
    exact ⟨_, hx, incl_val A K h x⟩
  · rintro ⟨y, hy, he⟩
    have : y = incl A K h x := Subtype.ext (Subtype.ext (he.trans (incl_val A K h x).symm))
    rwa [← this]

theorem mem_smul_iff {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0]
    [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
    (g : Pi1 A K) (Q : Ideal (CurveCoh.proChart A K R0)) (b : CurveCoh.proChart A K R0) :
    b ∈ g • Q ↔ ∃ c ∈ Q, (b : maxUnram A K) = g (c : maxUnram A K) := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hb
    refine ⟨_, hb, ?_⟩
    show (b : maxUnram A K) = g (g⁻¹ • (b : maxUnram A K))
    rw [← AlgEquiv.smul_def, smul_inv_smul]
  · rintro ⟨c, hc, he⟩
    have : g⁻¹ • b = c := Subtype.ext (by
      show g⁻¹ • (b : maxUnram A K) = c
      rw [he, ← AlgEquiv.smul_def, inv_smul_smul])
    rwa [this]

section Coh

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

theorem memZ1_triv (c : Γ → Λ) : c ∈ CurveCoh.Z1 (Representation.trivial Λ G Λ) Γ ↔
    IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h := by
  rw [CurveCoh.mem_Z1]
  simp only [Representation.trivial_apply]

theorem memZ1_sigma (σ : Representation Λ G Λ) (htr : ∀ (g : Γ) (x : Λ), σ g x = x) (d : Γ → Λ) :
    d ∈ CurveCoh.Z1 σ Γ ↔ IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h := by
  rw [CurveCoh.mem_Z1]
  simp only [htr]

theorem memZ1c_triv (x : (Γ → Λ) × (S → Λ)) : x ∈ CurveCoh.Z1c (Representation.trivial Λ G Λ) Γ I ↔
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) := by
  rw [CurveCoh.mem_Z1c, memZ1_triv]
  simp only [Representation.trivial_apply, sub_self, and_assoc]

theorem isPrim_iff (σ : Representation Λ G Λ) (htr : ∀ (g : Γ) (x : Λ), σ g x = x) (c d u : Γ → Λ) :
    CupDuality.IsPrim σ σ (LinearMap.mul Λ Λ) Γ c d u ↔
      IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g := by
  simp only [CupDuality.IsPrim, CupDuality.cupCochain, LinearMap.mul_apply', htr]

theorem eq_of_memB1c (x : (Γ → Λ) × (S → Λ))
    (hx : x ∈ CurveCoh.B1c (Representation.trivial Λ G Λ) Γ I) : ∃ m : Λ, x = (0, fun _ => m) := by
  obtain ⟨-, m, hm1, hm2⟩ := hx
  refine ⟨m, Prod.ext (funext fun g => ?_) (funext hm2)⟩
  rw [hm1 g]
  simp

end Coh

section Clauses

open CurveCoh CupDuality

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation Λ G Λ} {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)}

open Classical in
/-- The cup pairing on cochains: the pairing of the classes of `x` and `d` when both are cocycles, `0` otherwise. -/
noncomputable def cpair (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
    (DD : ConstData σ Γ I t) : (Γ → Λ) × (S → Λ) → (Γ → Λ) → Λ := fun x d =>
  if hx : x ∈ Z1c (Representation.trivial Λ G Λ) Γ I ∧ d ∈ Z1 σ Γ then
    constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx.1⟩) (H1.mk σ Γ ⟨d, hx.2⟩)
  else 0

theorem cpair_mk (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
    (DD : ConstData σ Γ I t) {x : (Γ → Λ) × (S → Λ)} {d : Γ → Λ}
    (hx : x ∈ Z1c (Representation.trivial Λ G Λ) Γ I) (hd : d ∈ Z1 σ Γ) :
    cpair H DD x d =
      constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx⟩) (H1.mk σ Γ ⟨d, hd⟩) := by
  rw [cpair, dif_pos ⟨hx, hd⟩]

variable (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
  (DD : ConstData σ Γ I t) (htr : ∀ (g : Γ) (x : Λ), σ g x = x)

include H htr in
theorem clause_cup : ∀ c d : Γ → Λ, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h) →
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    ∃ u : Γ → Λ, IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g := by
  intro c d hc hd
  obtain ⟨u, hu⟩ := exists_prim H ((memZ1_triv Γ c).2 hc) ((memZ1_sigma Γ σ htr d).2 hd)
  exact ⟨u, (isPrim_iff Γ σ htr c d u).1 hu⟩

include htr in
theorem clause_formula : ∀ (x : (Γ → Λ) × (S → Λ)) (d u : Γ → Λ),
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    (IsLocallyConstant u ∧ ∀ g h, x.1 g * d h = u h - u (g * h) + u g) →
    cpair H DD x d = ∑ s, (x.2 s * d (tG t s) - u (tG t s)) := by
  intro x d u hx hd hu
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  rw [cpair_mk H DD hx' hd']
  exact constPair_mk H DD ⟨x, hx'⟩ ⟨d, hd'⟩ u ((isPrim_iff Γ σ htr x.1 d u).2 hu)

include htr in
theorem clause_left (hperf : (constPair H DD).IsPerfPair) : ∀ x : (Γ → Λ) × (S → Λ),
    (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
      ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
    (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → cpair H DD x d = 0) →
    x.1 = 0 ∧ ∃ a : Λ, ∀ s, x.2 s = a := by
  intro x hx h0
  have hbl := LinearMap.IsPerfPair.bijective_left (constPair H DD)
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hB : constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) = 0 := by
    refine LinearMap.ext fun Y => ?_
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ Y
    have h1 := h0 d.1 ((memZ1_sigma Γ σ htr d.1).1 d.2)
    rw [cpair_mk H DD hx' d.2] at h1
    exact h1
  have hX : H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩ = 0 :=
    hbl.1 (hB.trans (map_zero _).symm)
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hX
  obtain ⟨m, hm⟩ := eq_of_memB1c Γ I x hmem
  subst hm
  exact ⟨rfl, m, fun _ => rfl⟩

include htr in
theorem clause_right (hperf : (constPair H DD).IsPerfPair) : ∀ d : Γ → Λ,
    (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
    (∀ x : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → cpair H DD x d = 0) →
    d = 0 := by
  intro d hd h0
  have hbr := LinearMap.IsPerfPair.bijective_right (constPair H DD)
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  have hB : (constPair H DD).flip (H1.mk σ Γ ⟨d, hd'⟩) = 0 := by
    refine LinearMap.ext fun X => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ X
    have h1 := h0 x.1 ((memZ1c_triv Γ I x.1).1 x.2)
    rw [cpair_mk H DD x.2 hd'] at h1
    exact h1
  have hY : H1.mk σ Γ ⟨d, hd'⟩ = 0 := hbr.1 (hB.trans (map_zero _).symm)
  obtain ⟨-, m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).1 hY
  funext g
  have h1 : d g = σ g m - m := hm g
  rw [h1, htr g m, sub_self]
  rfl

include htr in
theorem clause_surjL (hperf : (constPair H DD).IsPerfPair) : ∀ f : (Γ → Λ) → Λ,
    (∀ d d' : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) → f (d + d') = f d + f d') →
    (∀ (a : Λ) (d : Γ → Λ), (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      f (a • d) = a * f d) →
    ∃ x : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) ∧
      ∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → cpair H DD x d = f d := by
  intro f hadd hsmul
  have hbl := LinearMap.IsPerfPair.bijective_left (constPair H DD)
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0 ⟨IsLocallyConstant.zero, fun _ _ => by simp⟩
      ⟨IsLocallyConstant.zero, fun _ _ => by simp⟩
    rw [add_zero] at h
    exact (add_eq_left.1 h.symm)
  let f0 : Z1 σ Γ →ₗ[Λ] Λ :=
    { toFun := fun d => f d.1
      map_add' := fun d d' => hadd d.1 d'.1 ((memZ1_sigma Γ σ htr _).1 d.2)
        ((memZ1_sigma Γ σ htr _).1 d'.2)
      map_smul' := fun a d => hsmul a d.1 ((memZ1_sigma Γ σ htr _).1 d.2) }
  let f00 := ((B1 σ Γ).comap (Z1 σ Γ).subtype).liftQ f0 (by
    intro d hd
    obtain ⟨-, m, hm⟩ := hd
    have : d.1 = 0 := funext fun g => by
      have h1 : d.1 g = σ g m - m := hm g
      rw [h1, htr g m, sub_self]
      rfl
    show f d.1 = 0
    rw [this, hf0])
  obtain ⟨X, hX⟩ := hbl.2 f00
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ X
  refine ⟨x.1, (memZ1c_triv Γ I x.1).1 x.2, fun d hd => ?_⟩
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  rw [cpair_mk H DD x.2 hd']
  exact LinearMap.congr_fun hX (H1.mk σ Γ ⟨d, hd'⟩)

include htr in
theorem clause_surjR (hperf : (constPair H DD).IsPerfPair) : ∀ f : (Γ → Λ) × (S → Λ) → Λ,
    (∀ x y : (Γ → Λ) × (S → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
      (IsLocallyConstant y.1 ∧ (∀ g h, y.1 (g * h) = y.1 g + y.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → y.1 g = 0) → f (x + y) = f x + f y) →
    (∀ (a : Λ) (x : (Γ → Λ) × (S → Λ)),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → f (a • x) = a * f x) →
    (∀ a : Λ, f (0, fun _ => a) = 0) →
    ∃ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) ∧
      ∀ x : (Γ → Λ) × (S → Λ),
        (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
          ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) → cpair H DD x d = f x := by
  intro f hadd hsmul h0
  have hbr := LinearMap.IsPerfPair.bijective_right (constPair H DD)
  let f0 : Z1c (Representation.trivial Λ G Λ) Γ I →ₗ[Λ] Λ :=
    { toFun := fun x => f x.1
      map_add' := fun x y => hadd x.1 y.1 ((memZ1c_triv Γ I _).1 x.2) ((memZ1c_triv Γ I _).1 y.2)
      map_smul' := fun a x => hsmul a x.1 ((memZ1c_triv Γ I _).1 x.2) }
  let f00 := ((B1c (Representation.trivial Λ G Λ) Γ I).comap
    (Z1c (Representation.trivial Λ G Λ) Γ I).subtype).liftQ f0 (by
    intro x hx
    obtain ⟨m, hm⟩ := eq_of_memB1c Γ I x.1 hx
    show f x.1 = 0
    rw [hm]
    exact h0 m)
  obtain ⟨Y, hY⟩ := hbr.2 f00
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ Y
  refine ⟨d.1, (memZ1_sigma Γ σ htr d.1).1 d.2, fun x hx => ?_⟩
  have hx' := (memZ1c_triv Γ I x).2 hx
  rw [cpair_mk H DD hx' d.2]
  exact LinearMap.congr_fun hY (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩)

include htr in
theorem clause_frob [Γ.Normal] (φ : G) (τ : S → S) (η : S → Γ) (hI : BdryCompat Γ I φ⁻¹ τ η) (c0 : Λ)
    (key : ∀ x y, constPair H DD (frobH1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI x)
      (frobH1 σ Γ φ⁻¹ y) = c0 * constPair H DD x y) :
    ∀ (x : (Γ → Λ) × (S → Λ)) (d c' d' : Γ → Λ),
      (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → x.1 g = 0) →
      (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
      (∀ g g' : Γ, (g' : G) = φ * g * φ⁻¹ → c' g = x.1 g' ∧ d' g = σ φ⁻¹ (d g')) →
      (IsLocallyConstant c' ∧ (∀ g h, c' (g * h) = c' g + c' h) ∧
        ∀ s (g : Γ), (g : G) ∈ I s → c' g = 0) ∧
      (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) ∧
      cpair H DD (c', fun s => x.2 (τ s) - x.1 (η s)) d' = c0 * cpair H DD x d := by
  intro x d c' d' hx hd hrel
  have hx' := (memZ1c_triv Γ I x).2 hx
  have hd' := (memZ1_sigma Γ σ htr d).2 hd
  have hconj : ∀ g, ((conjΓ Γ φ⁻¹ g : Γ) : G) = φ * g * φ⁻¹ := fun g => by
    rw [conjΓ_val, inv_inv]
  have hc' : c' = twist (Representation.trivial Λ G Λ) Γ φ⁻¹ x.1 := funext fun g => by
    rw [twist_apply, Representation.trivial_apply]
    exact (hrel g _ (hconj g)).1
  have hdd : d' = twist σ Γ φ⁻¹ d := funext fun g => by
    rw [twist_apply]
    exact (hrel g _ (hconj g)).2
  subst hc' hdd
  have hpair : ((twist (Representation.trivial Λ G Λ) Γ φ⁻¹ x.1, fun s => x.2 (τ s) - x.1 (η s)) :
      (Γ → Λ) × (S → Λ)) = twistc (Representation.trivial Λ G Λ) Γ φ⁻¹ τ η x := by
    refine Prod.ext rfl (funext fun s => ?_)
    rw [twistc_snd]
    simp only [Representation.trivial_apply]
  have hZc := twistc_mem_Z1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI hx'
  have hZ1 := twist_mem_Z1 σ Γ φ⁻¹ hd'
  rw [← hpair] at hZc
  refine ⟨(memZ1c_triv Γ I _).1 hZc, (memZ1_sigma Γ σ htr _).1 hZ1, ?_⟩
  rw [cpair_mk H DD hZc hZ1, cpair_mk H DD hx' hd']
  have e := key (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) (H1.mk σ Γ ⟨d, hd'⟩)
  have hX : H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨_, hZc⟩ =
      frobH1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ η hI
        (H1c.mk (Representation.trivial Λ G Λ) Γ I ⟨x, hx'⟩) := by
    simp only [frobH1c, H1c.mk, Submodule.mkQ_apply]
    exact congrArg _ (Subtype.ext hpair)
  have hY : H1.mk σ Γ ⟨_, hZ1⟩ = frobH1 σ Γ φ⁻¹ (H1.mk σ Γ ⟨d, hd'⟩) := by
    simp only [frobH1, H1.mk, Submodule.mkQ_apply]
    rfl
  exact (congrArg₂ (fun a b => constPair H DD a b) hX hY).trans e

end Clauses

end CDBridge
end RamanujanPetersson


