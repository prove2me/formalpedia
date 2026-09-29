-- Prove2me | Definitions.Def_CuspForm_TWLevelHeckeRing
-- name    : CuspForm_TWLevelHeckeRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/042b8b89-6d44-57c4-86d7-f9e3a3ca9064
-- title:
--   Hecke ring acting on the Taylor–Wiles level cohomology module
-- statement:
--   Standing context: natural numbers $N,r$ and a tuple $q_1,\dots,q_t$ (all nonzero), $L=\mathrm{level}=N\cdot(\prod_i q_i)\cdot r$, a set $S$ of natural numbers, a local ring $\mathcal O$ with residue field $k$, a subgroup $H\le(\mathbb Z/L)^\times$, a ring homomorphism $\theta$ from the weight-two level-$N$ Hecke algebra away from $S$ to $k$, scalars $\alpha_i\in k$, and proofs `hc`, `hdc` that the operators $T_\ell,U_{q_i}$ on the carrier $H^1=\mathrm{Hom}(\Gamma_H(L)^{\mathrm{add}},\mathcal O)$ commute with one another and with all $\langle u\rangle$. The module $ML$ is the localisation of that carrier at the prime $\mathfrak m_\theta=\ker(\tilde\theta)$ of the polynomial algebra on the generator symbols.
--
--   First, properties of the diamond operators on $H^1$: the raw conjugation operator satisfies $\mathrm{diamondRaw}\,\sigma\circ\mathrm{diamondRaw}\,\tau=\mathrm{diamondRaw}(\tau\sigma)$, whence the operator $\mathrm{diamondL}$ attached to $u\in(\mathbb Z/M)^\times$ (defined via a chosen lift in $\Gamma_0(M)$) is multiplicative, sends $1$ to $1$, commutes with itself, and equals the identity for $u\in H$ (the lift then lies in $\Gamma_H(M)$ and the change is an inner automorphism, which acts trivially on homomorphisms to $\mathcal O$). These transfer to the operators $\mathrm{diaML}$ on $ML$.
--
--   Then `opML` is the $\mathcal O$-algebra map sending a polynomial $f$ to multiplication by $f$ on $ML$, and `heckeRingGens` is the set consisting of the operators $\mathrm{opML}(X_{T_\ell})$ for primes $\ell\notin S$ with $\ell\nmid L$ together with the operators $\mathrm{diaML}(u)$ for $u$ in $HR=\ker((\mathbb Z/L)^\times\to(\mathbb Z/r)^\times)$; no $U_{q_i}$ and no diamond outside $HR$ is among the generators. These pairwise commute, so `heckeSubalgebra`, the $\mathcal O$-subalgebra of $\mathrm{End}_{\mathcal O}(ML)$ they generate, is commutative; `HeckeRing` is its underlying type, carrying commutative ring and $\mathcal O$-algebra structures, the injective action `act` by the inclusion, named elements `T` and `diamond`, the relations $\langle uv\rangle=\langle u\rangle\langle v\rangle$, $\langle1\rangle=1$, $\langle u\rangle=1$ for $u\in HR\cap H$, invertibility of each $\langle u\rangle$, and the fact that the whole subalgebra lies in the centraliser of the image of `opML` (so its elements commute with the $U_{q_i}$ as well).
--
--   **Relation to Mathlib.** Built from Mathlib's `Algebra.adjoin`, `Module.End`, `Subalgebra.centralizer` and `LocalizedModule`, but the Hecke ring acting on the localised cohomology of $\Gamma_H(L)$, and its diamond operators, are the project's own notions.
--
--   **Where it is used.** These rings are the Hecke rings at Taylor–Wiles auxiliary level $L=N\,q_1\cdots q_t\,r$ acting on the localised cohomology module used in the modularity-lifting argument; the relation $\langle u\rangle=1$ for $u\in HR\cap H$ is what makes the diamond action factor through the relevant quotient of $(\mathbb Z/L)^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_TWLevelHeckeRing.lean

import Definitions.Def_CuspForm_TWLevelHeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace CohCarrier

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪]

theorem diamondRaw_diamondRaw (σ τ : CongruenceSubgroup.Gamma0 M) (φ : H1 M H 𝒪) :
    diamondRaw M H 𝒪 σ (diamondRaw M H 𝒪 τ φ) = diamondRaw M H 𝒪 (τ * σ) φ := by
  ext γ
  show φ (Additive.ofMul (conjHom M H τ (conjHom M H σ (Additive.toMul γ)))) =
    φ (Additive.ofMul (conjHom M H (τ * σ) (Additive.toMul γ)))
  congr 2
  apply Subtype.ext
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
  group

theorem diamondL_mul [NeZero M] (u v : (ZMod M)ˣ) :
    diamondL M H 𝒪 (u * v) = diamondL M H 𝒪 u * diamondL M H 𝒪 v := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M u
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective M v
  apply LinearMap.ext
  intro φ
  rw [Module.End.mul_apply, diamondL_eq_diamondRaw M H 𝒪 v τ hτ,
    diamondL_eq_diamondRaw M H 𝒪 u σ hσ, diamondRaw_diamondRaw,
    diamondL_eq_diamondRaw M H 𝒪 (u * v) (τ * σ) (by rw [map_mul, hσ, hτ, mul_comm])]

theorem diamondL_one [NeZero M] : diamondL M H 𝒪 1 = 1 := by
  apply LinearMap.ext
  intro φ
  rw [diamondL_eq_diamondRaw M H 𝒪 1 1 (map_one _)]
  ext γ
  show φ (Additive.ofMul (conjHom M H 1 (Additive.toMul γ))) = φ γ
  congr 1
  have : conjHom M H 1 (Additive.toMul γ) = Additive.toMul γ := Subtype.ext (by simp [conjHom])
  rw [this]
  rfl

theorem diamondL_comm [NeZero M] (u v : (ZMod M)ˣ) :
    diamondL M H 𝒪 u * diamondL M H 𝒪 v = diamondL M H 𝒪 v * diamondL M H 𝒪 u := by
  rw [← diamondL_mul, ← diamondL_mul, mul_comm]

theorem diamondL_of_mem [NeZero M] (u : (ZMod M)ˣ) (hu : u ∈ H) : diamondL M H 𝒪 u = 1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M u
  have hσH : (σ : SL(2, ℤ)) ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    refine ⟨σ.2, ?_⟩
    have e : (⟨(σ : SL(2, ℤ)), σ.2⟩ : CongruenceSubgroup.Gamma0 M) = σ := Subtype.coe_eta _ _
    rw [e, hσ]
    exact hu
  apply LinearMap.ext
  intro φ
  rw [diamondL_eq_diamondRaw M H 𝒪 u σ hσ]
  ext γ
  show φ (Additive.ofMul (conjHom M H σ (Additive.toMul γ))) = φ γ
  set κ : ↥(GammaH M H) := ⟨(σ : SL(2, ℤ)), hσH⟩ with hκ
  have hconj : conjHom M H σ (Additive.toMul γ) = κ * Additive.toMul γ * κ⁻¹ :=
    Subtype.ext (by simp [conjHom, hκ])
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp only [ofMul_toMul, add_neg_cancel_comm]

end Diamond

end CohCarrier

namespace CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

omit [NeZero r] in

def opML : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  Algebra.lsmul 𝒪 𝒪 (ML N r qv S 𝒪 H θ α hc)

omit [NeZero r] in
@[simp] theorem opML_apply (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg)
    (x : ML N r qv S 𝒪 H θ α hc) : opML N r qv S 𝒪 H θ α hc f x = f • x := rfl

theorem diaML_mul (u v : (ZMod (level N r qv))ˣ) :
    diaML N r qv S 𝒪 H θ α hc hdc (u * v) =
      diaML N r qv S 𝒪 H θ α hc hdc u * diaML N r qv S 𝒪 H θ α hc hdc v := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc (u * v)) (LocalizedModule.mk m s) =
      LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc u)
        (LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc v) (LocalizedModule.mk m s))
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    congr 1
    show CohCarrier.diamondL (level N r qv) H 𝒪 (u * v) m =
      CohCarrier.diamondL (level N r qv) H 𝒪 u (CohCarrier.diamondL (level N r qv) H 𝒪 v m)
    rw [CohCarrier.diamondL_mul]
    rfl

theorem diaML_one : diaML N r qv S 𝒪 H θ α hc hdc 1 = 1 := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc 1) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    congr 1
    show CohCarrier.diamondL (level N r qv) H 𝒪 1 m = m
    rw [CohCarrier.diamondL_one]
    rfl

theorem diaML_of_mem (u : (ZMod (level N r qv))ˣ) (hu : u ∈ H) :
    diaML N r qv S 𝒪 H θ α hc hdc u = 1 := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (diamondLin N r qv S 𝒪 H θ α hc hdc u) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    congr 1
    show CohCarrier.diamondL (level N r qv) H 𝒪 u m = m
    rw [CohCarrier.diamondL_of_mem _ _ _ u hu]
    rfl

theorem diaML_comm (u v : (ZMod (level N r qv))ˣ) :
    diaML N r qv S 𝒪 H θ α hc hdc u * diaML N r qv S 𝒪 H θ α hc hdc v =
      diaML N r qv S 𝒪 H θ α hc hdc v * diaML N r qv S 𝒪 H θ α hc hdc u := by
  rw [← diaML_mul, ← diaML_mul, mul_comm]

theorem opML_mul_diaML (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) (u : (ZMod (level N r qv))ˣ) :
    opML N r qv S 𝒪 H θ α hc f * diaML N r qv S 𝒪 H θ α hc hdc u =
      diaML N r qv S 𝒪 H θ α hc hdc u * opML N r qv S 𝒪 H θ α hc f :=
  LinearMap.ext fun x => (diaML_smul N r qv S 𝒪 H θ α hc hdc u f x).symm

def heckeRingGens : Set (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      T = opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL))} ∪
  {D | ∃ u ∈ HR N r qv, D = diaML N r qv S 𝒪 H θ α hc hdc u}

theorem heckeRingGens_comm :
    ∀ a ∈ heckeRingGens N r qv S 𝒪 H θ α hc hdc, ∀ b ∈ heckeRingGens N r qv S 𝒪 H θ α hc hdc,
      a * b = b * a := by
  rintro a (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩) b (⟨ℓ', hℓ', hℓS', hℓL', rfl⟩ | ⟨v, hv, rfl⟩)
  · rw [← map_mul, ← map_mul, mul_comm]
  · exact opML_mul_diaML N r qv S 𝒪 H θ α hc hdc _ v
  · exact (opML_mul_diaML N r qv S 𝒪 H θ α hc hdc _ u).symm
  · exact diaML_comm N r qv S 𝒪 H θ α hc hdc u v

def heckeSubalgebra : Subalgebra 𝒪 (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  Algebra.adjoin 𝒪 (heckeRingGens N r qv S 𝒪 H θ α hc hdc)

instance heckeSubalgebra_isMulCommutative :
    IsMulCommutative ↥(heckeSubalgebra N r qv S 𝒪 H θ α hc hdc) :=
  Algebra.isMulCommutative_adjoin 𝒪 (heckeRingGens_comm N r qv S 𝒪 H θ α hc hdc)

def HeckeRing : Type := ↥(heckeSubalgebra N r qv S 𝒪 H θ α hc hdc)

instance HeckeRing.instCommRing : CommRing (HeckeRing N r qv S 𝒪 H θ α hc hdc) :=
  { (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).toRing with
    mul_comm := (heckeSubalgebra_isMulCommutative N r qv S 𝒪 H θ α hc hdc).is_comm.comm }

instance HeckeRing.instAlgebra : Algebra 𝒪 (HeckeRing N r qv S 𝒪 H θ α hc hdc) :=
  (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).algebra

instance HeckeRing.instModuleSelf :
    @Module (HeckeRing N r qv S 𝒪 H θ α hc hdc) (HeckeRing N r qv S 𝒪 H θ α hc hdc) _
      AddCommGroup.toAddCommMonoid :=
  Semiring.toModule

instance HeckeRing.instInhabited : Inhabited (HeckeRing N r qv S 𝒪 H θ α hc hdc) := ⟨0⟩

namespace HeckeRing

def act : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) :=
  (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).val

theorem act_apply (x : HeckeRing N r qv S 𝒪 H θ α hc hdc) :
    act N r qv S 𝒪 H θ α hc hdc x = (Subtype.val x : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) := rfl

theorem act_injective : Function.Injective (act N r qv S 𝒪 H θ α hc hdc) :=
  Subtype.val_injective

theorem mem_heckeSubalgebra (x : HeckeRing N r qv S 𝒪 H θ α hc hdc) :
    act N r qv S 𝒪 H θ α hc hdc x ∈ heckeSubalgebra N r qv S 𝒪 H θ α hc hdc := x.2

@[ext] theorem ext {x y : HeckeRing N r qv S 𝒪 H θ α hc hdc}
    (h : act N r qv S 𝒪 H θ α hc hdc x = act N r qv S 𝒪 H θ α hc hdc y) : x = y :=
  act_injective N r qv S 𝒪 H θ α hc hdc h

def T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    HeckeRing N r qv S 𝒪 H θ α hc hdc :=
  ⟨opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)),
    Algebra.subset_adjoin (Or.inl ⟨ℓ, hℓ, hℓS, hℓL, rfl⟩)⟩

@[simp] theorem act_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    act N r qv S 𝒪 H θ α hc hdc (T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) =
      opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL)) := rfl

theorem act_T_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
    (x : ML N r qv S 𝒪 H θ α hc) :
    act N r qv S 𝒪 H θ α hc hdc (T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) x =
      (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL) : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • x := rfl

def diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) : HeckeRing N r qv S 𝒪 H θ α hc hdc :=
  ⟨diaML N r qv S 𝒪 H θ α hc hdc u, Algebra.subset_adjoin (Or.inr ⟨u, hu, rfl⟩)⟩

@[simp] theorem act_diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    act N r qv S 𝒪 H θ α hc hdc (diamond N r qv S 𝒪 H θ α hc hdc u hu) =
      diaML N r qv S 𝒪 H θ α hc hdc u := rfl

theorem diamond_mul (u v : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) (hv : v ∈ HR N r qv) :
    diamond N r qv S 𝒪 H θ α hc hdc (u * v) (mul_mem hu hv) =
      diamond N r qv S 𝒪 H θ α hc hdc u hu * diamond N r qv S 𝒪 H θ α hc hdc v hv :=
  ext N r qv S 𝒪 H θ α hc hdc (by rw [map_mul, act_diamond, act_diamond, act_diamond, diaML_mul])

theorem diamond_one : diamond N r qv S 𝒪 H θ α hc hdc 1 (one_mem _) = 1 :=
  ext N r qv S 𝒪 H θ α hc hdc (by rw [map_one, act_diamond, diaML_one])

theorem diamond_eq_one_of_mem (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) (huH : u ∈ H) :
    diamond N r qv S 𝒪 H θ α hc hdc u hu = 1 :=
  ext N r qv S 𝒪 H θ α hc hdc (by rw [map_one, act_diamond, diaML_of_mem _ _ _ _ _ _ _ _ _ _ u huH])

theorem isUnit_diamond (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    IsUnit (diamond N r qv S 𝒪 H θ α hc hdc u hu) :=
  IsUnit.of_mul_eq_one (diamond N r qv S 𝒪 H θ α hc hdc u⁻¹ (inv_mem hu))
    (ext N r qv S 𝒪 H θ α hc hdc (by
      rw [map_mul, act_diamond, act_diamond, ← diaML_mul, mul_inv_cancel, diaML_one, map_one]))

theorem diamond_mul_diamond_inv (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    diamond N r qv S 𝒪 H θ α hc hdc u hu * diamond N r qv S 𝒪 H θ α hc hdc u⁻¹ (inv_mem hu) = 1 :=
  ext N r qv S 𝒪 H θ α hc hdc (by
    rw [map_mul, act_diamond, act_diamond, ← diaML_mul, mul_inv_cancel, diaML_one, map_one])

theorem heckeSubalgebra_le_centralizer :
    heckeSubalgebra N r qv S 𝒪 H θ α hc hdc ≤
      Subalgebra.centralizer 𝒪 (Set.range (opML N r qv S 𝒪 H θ α hc)) := by
  refine Algebra.adjoin_le ?_
  rintro a (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩)
  · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨f, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨f, rfl⟩
    exact opML_mul_diaML N r qv S 𝒪 H θ α hc hdc f u

theorem act_mul_opML (x : HeckeRing N r qv S 𝒪 H θ α hc hdc)
    (f : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) :
    act N r qv S 𝒪 H θ α hc hdc x * opML N r qv S 𝒪 H θ α hc f =
      opML N r qv S 𝒪 H θ α hc f * act N r qv S 𝒪 H θ α hc hdc x :=
  ((Subalgebra.mem_centralizer_iff 𝒪).mp (heckeSubalgebra_le_centralizer N r qv S 𝒪 H θ α hc hdc x.2)
    (opML N r qv S 𝒪 H θ α hc f) ⟨f, rfl⟩).symm

end HeckeRing

end CuspForm.TWLevel

end


