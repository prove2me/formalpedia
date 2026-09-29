-- Prove2me | Definitions.Def_IharaLemma_IdempotentSplitting
-- name    : IharaLemma_IdempotentSplitting
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7c2b0e7b-40d7-5a54-b2b1-aa92301b87d4
-- title:
--   Idempotent splittings of semilocal rings and corner rings
-- statement:
--   For a commutative ring $B$, the structure [`IharaLemma.IdempotentSplitting B`](../def/IharaLemma_IdempotentSplitting.html#L7) bundles: a natural number $n$; a family $e : \mathrm{Fin}\,n \to B$; a family $\mathfrak{m} : \mathrm{Fin}\,n \to$ (ideals of $B$); a proof that $e$ is a complete orthogonal family of idempotents in Mathlib's sense (`CompleteOrthogonalIdempotents`); proofs that each $\mathfrak{m}\,i$ is maximal and that every maximal ideal of $B$ equals some $\mathfrak{m}\,i$; and the incidence condition $e\,i \in \mathfrak{m}\,j \iff i \neq j$. So the data present $B$ as a semilocal ring whose finitely many maximal ideals are enumerated, with an idempotent attached to each, the theorems being carried as fields. Immediate consequences recorded are the injectivity of $i \mapsto \mathfrak{m}\,i$, that $e\,i \notin \mathfrak{m}\,i$, that $e\,i$ lies in every maximal ideal distinct from $\mathfrak{m}\,i$, and idempotency of each $e\,i$.
--
--   For a $B$-module $M$ and $e \in B$, `cornerSubmodule e` is the image of the $B$-linear map $m \mapsto e \cdot m$, and `toCorner e` is that map viewed as a surjection onto it. The ring-theoretic counterpart is `CornerRing S i`, Mathlib's corner $e\,i\,B\,e\,i$ of the idempotent $e\,i$ (with unit element $e\,i$), together with the ring homomorphism `toCornerRing`, $b \mapsto e\,i \cdot b \cdot e\,i$, the induced algebra structure over $B$ and over any base ring $\mathcal{O}$ mapping to $B$, and the corresponding scalar towers. Two facts are proved about it: `CornerRing S i` is a localisation of $B$ at the prime complement of $\mathfrak{m}\,i$, hence a local ring. The underlying invertibility input is `exists_mul_mul_eq_of_notMem`: if $e$ is idempotent and lies in every maximal ideal other than $\mathfrak{m}$, then for $s \notin \mathfrak{m}$ there is $t$ with $t s e = e$. Finally, $e\,i \cdot M$ is made a module over `CornerRing S i`, compatibly with the $B$- and $\mathcal{O}$-actions, and `cornerRingLinearEquiv` is the $\mathcal{O}$-linear isomorphism between `CornerRing S i` and the corner submodule $e\,i \cdot B$ of $B$ itself, both realised by the same underlying elements of $B$.
--
--   **Relation to Mathlib.** Built on Mathlib's `CompleteOrthogonalIdempotents` and on the corner ring `IsIdempotentElem.Corner` of an idempotent; the bundled structure pairing a complete orthogonal family of idempotents with a bijective enumeration of the maximal ideals, and the module-level `cornerSubmodule`, are the project's own.
--
--   **Where it is used.** The data package the decomposition of a semilocal commutative ring — typically a Hecke algebra acting on a space of modular forms or on a cohomology module — into its local factors, and transfer modules to the corresponding direct summands. This is the bookkeeping used when arguments of Ihara type and modularity-lifting arguments are localised at a single maximal ideal of a Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaLemma_IdempotentSplitting.lean

import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace IharaLemma

structure IdempotentSplitting (B : Type) [CommRing B] where
  n : ℕ
  e : Fin n → B
  𝔪 : Fin n → Ideal B
  coi : CompleteOrthogonalIdempotents e
  isMaximal : ∀ i, (𝔪 i).IsMaximal
  exists_eq : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I
  mem_iff : ∀ i j, e i ∈ 𝔪 j ↔ i ≠ j

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)

theorem 𝔪_injective : Function.Injective S.𝔪 := by
  intro i j h
  by_contra hij
  have h1 : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr hij
  rw [← h] at h1
  exact ((S.mem_iff i i).mp h1) rfl

theorem notMem (i : Fin S.n) : S.e i ∉ S.𝔪 i := fun h => ((S.mem_iff i i).mp h) rfl

theorem mem_of_ne {i j : Fin S.n} (h : i ≠ j) : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr h

theorem mem_of_isMaximal_of_ne (i : Fin S.n) (J : Ideal B) (hJ : J.IsMaximal) (hne : J ≠ S.𝔪 i) :
    S.e i ∈ J := by
  obtain ⟨j, rfl⟩ := S.exists_eq J hJ
  exact S.mem_of_ne fun h => hne (congrArg S.𝔪 h.symm)

theorem idem (i : Fin S.n) : IsIdempotentElem (S.e i) := S.coi.idem i

instance isMaximal_𝔪 (i : Fin S.n) : (S.𝔪 i).IsMaximal := S.isMaximal i

end IdempotentSplitting

section CornerModule

variable {B : Type} [CommRing B] {M : Type} [AddCommGroup M] [Module B M]

def cornerSubmodule (e : B) : Submodule B M := LinearMap.range (e • (LinearMap.id : M →ₗ[B] M))

def toCorner (e : B) : M →ₗ[B] cornerSubmodule (M := M) e :=
  LinearMap.rangeRestrict (e • (LinearMap.id : M →ₗ[B] M))

@[simp] theorem toCorner_apply (e : B) (v : M) :
    ((toCorner (M := M) e v : cornerSubmodule e) : M) = e • v := rfl

end CornerModule

theorem exists_mul_mul_eq_of_notMem {B : Type} [CommRing B] {e : B} (he : IsIdempotentElem e)
    (𝔪 : Ideal B) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) {s : B} (hs : s ∉ 𝔪) :
    ∃ t : B, t * s * e = e := by
  have htop : Ideal.span {s} ⊔ Ideal.span {1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1e : 1 - e ∈ J := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hsJ : s ∈ J := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hJ𝔪 : J ≠ 𝔪 := fun h => hs (h ▸ hsJ)
    have heJ : e ∈ J := hother J hJ hJ𝔪
    apply hJ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := J.add_mem heJ h1e
    rwa [add_sub_cancel] at this
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have key : t * s * e + u * ((1 - e) * e) = 1 * e := by
    have := congrArg (· * e) hab
    simpa only [add_mul, mul_assoc] using this
  rwa [h0, mul_zero, add_zero, one_mul] at key

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)

abbrev CornerRing : Type := (S.idem i).Corner

instance coeOutCornerRing : CoeOut (S.CornerRing i) B := ⟨Subtype.val⟩

theorem coe_mk_cornerRing (x : B) (hx) : ((⟨x, hx⟩ : S.CornerRing i) : B) = x := rfl

@[ext] theorem ext_cornerRing {z w : S.CornerRing i} (h : (z : B) = w) : z = w := Subtype.ext h

theorem coe_one_cornerRing : ((1 : S.CornerRing i) : B) = S.e i := rfl

def toCornerRing : B →+* S.CornerRing i where
  toFun b := ⟨S.e i * b * S.e i, b, rfl⟩
  map_one' := Subtype.ext (by
    show S.e i * 1 * S.e i = S.e i
    rw [mul_one, (S.idem i).eq])
  map_mul' a b := Subtype.ext (by
    show S.e i * (a * b) * S.e i = S.e i * a * S.e i * (S.e i * b * S.e i)
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (-(a * b) * (S.e i * S.e i + S.e i)) * h2)
  map_zero' := Subtype.ext (by
    show S.e i * 0 * S.e i = 0
    rw [mul_zero, zero_mul])
  map_add' a b := Subtype.ext (by
    show S.e i * (a + b) * S.e i = S.e i * a * S.e i + S.e i * b * S.e i
    rw [mul_add, add_mul])

@[simp] theorem coe_toCornerRing (b : B) :
    ((S.toCornerRing i b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl

theorem e_mul_coe (z : S.CornerRing i) : S.e i * (z : B) = z := by
  obtain ⟨_, a, rfl⟩ := z
  show S.e i * (S.e i * a * S.e i) = S.e i * a * S.e i
  rw [← mul_assoc, ← mul_assoc, (S.idem i).eq]

theorem coe_mul_e (z : S.CornerRing i) : (z : B) * S.e i = z := by
  rw [mul_comm]; exact S.e_mul_coe i z

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

instance algebraBaseCornerRing : Algebra 𝒪 (S.CornerRing i) :=
  ((S.toCornerRing i).comp (algebraMap 𝒪 B)).toAlgebra

instance isScalarTower_base_cornerRing : IsScalarTower 𝒪 B (S.CornerRing i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_base_cornerRing_coe (r : 𝒪) :
    ((algebraMap 𝒪 (S.CornerRing i) r : S.CornerRing i) : B) = S.e i * algebraMap 𝒪 B r * S.e i :=
  rfl

end Base

theorem algebraMap_cornerRing_coe (b : B) :
    ((algebraMap B (S.CornerRing i) b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl

instance isLocalization_cornerRing : IsLocalization (S.𝔪 i).primeCompl (S.CornerRing i) where
  map_units y := by
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem i) (S.𝔪 i) (S.mem_of_isMaximal_of_ne i) y.2
    refine IsUnit.of_mul_eq_one (algebraMap B (S.CornerRing i) t) (Subtype.ext ?_)
    show S.e i * (y : B) * S.e i * (S.e i * t * S.e i) = S.e i
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (t * (y : B) * (S.e i * S.e i + S.e i + 1)) * h2 + ht
  surj z := by
    obtain ⟨_, a, rfl⟩ := z
    refine ⟨(S.e i * a * S.e i, 1), Subtype.ext ?_⟩
    show S.e i * a * S.e i * (S.e i * ((1 : (S.𝔪 i).primeCompl) : B) * S.e i)
        = S.e i * (S.e i * a * S.e i) * S.e i
    rw [OneMemClass.coe_one]
    ring
  exists_of_eq {x y} h := by
    refine ⟨⟨S.e i, S.notMem i⟩, ?_⟩
    have h' : S.e i * x * S.e i = S.e i * y * S.e i := congrArg Subtype.val h
    show S.e i * x = S.e i * y
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination h' + (y - x) * h2

instance isLocalRing_cornerRing : IsLocalRing (S.CornerRing i) :=
  IsLocalization.AtPrime.isLocalRing (S.CornerRing i) (S.𝔪 i)

section CornerModule

variable {M : Type} [AddCommGroup M] [Module B M]

theorem e_smul_coe (m : cornerSubmodule (M := M) (S.e i)) : S.e i • (m : M) = m := by
  obtain ⟨m0, hm0⟩ := m.2
  rw [← hm0]
  show S.e i • (S.e i • m0) = S.e i • m0
  rw [smul_smul, (S.idem i).eq]

theorem coe_smul_mem (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    (z : B) • (m : M) ∈ cornerSubmodule (M := M) (S.e i) :=
  ⟨(z : B) • (m : M), by
    show S.e i • ((z : B) • (m : M)) = (z : B) • (m : M)
    rw [smul_smul, S.e_mul_coe]⟩

instance smulCornerModule : SMul (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun z m => ⟨(z : B) • (m : M), S.coe_smul_mem i z m⟩⟩

theorem coe_zero_cornerRing : ((0 : S.CornerRing i) : B) = 0 := rfl

@[simp] theorem coe_cornerSmul (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    ((z • m : cornerSubmodule (M := M) (S.e i)) : M) = (z : B) • (m : M) := rfl

instance moduleCornerModule : Module (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) where
  one_smul m := Subtype.ext (by rw [coe_cornerSmul, coe_one_cornerRing, e_smul_coe])
  mul_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, coe_cornerSmul, coe_cornerSmul, ← mul_smul]; rfl)
  smul_zero x := Subtype.ext (by rw [coe_cornerSmul, ZeroMemClass.coe_zero, smul_zero])
  smul_add x m n := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, smul_add, AddMemClass.coe_add, coe_cornerSmul,
      coe_cornerSmul])
  add_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, coe_cornerSmul, coe_cornerSmul, ← add_smul]; rfl)
  zero_smul m := Subtype.ext (by
    rw [coe_cornerSmul, coe_zero_cornerRing, zero_smul, ZeroMemClass.coe_zero])

instance isScalarTower_cornerModule :
    IsScalarTower B (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun b z m => Subtype.ext (by
    show (S.e i * b * S.e i * (z : B)) • (m : M) = b • ((z : B) • (m : M))
    rw [mul_assoc, S.e_mul_coe, mul_comm (S.e i) b, mul_assoc, S.e_mul_coe, mul_smul])⟩

end CornerModule

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

noncomputable def cornerRingLinearEquiv :
    S.CornerRing i ≃ₗ[𝒪] ↥(cornerSubmodule (M := B) (S.e i)) where
  toFun x := ⟨x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b * S.e i, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination hb⟩
  invFun x := ⟨x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hy
    exact ⟨y, by linear_combination y * (S.idem i).eq + hy⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext (by
    obtain ⟨b, hb⟩ := x.2
    show (S.e i * algebraMap 𝒪 B r * S.e i) * (x : B) = r • (x : B)
    rw [Algebra.smul_def]
    linear_combination (algebraMap 𝒪 B r * b * (S.e i * S.e i + S.e i)) * (S.idem i).eq
      + (algebraMap 𝒪 B r - S.e i * algebraMap 𝒪 B r * S.e i) * hb)

@[simp] theorem cornerRingLinearEquiv_apply (x : S.CornerRing i) :
    ((cornerRingLinearEquiv S i 𝒪 x : cornerSubmodule (M := B) (S.e i)) : B) = (x : B) := rfl

@[simp] theorem cornerRingLinearEquiv_symm_apply (x : cornerSubmodule (M := B) (S.e i)) :
    (((cornerRingLinearEquiv S i 𝒪).symm x : S.CornerRing i) : B) = (x : B) := rfl

end Base

section BaseModule

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module 𝒪 M] [IsScalarTower 𝒪 B M]

instance isScalarTower_base_cornerModule :
    IsScalarTower 𝒪 (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun r z m => by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 B (S.CornerRing i) r, ← Algebra.smul_def,
      smul_assoc, algebraMap_smul]⟩

end BaseModule

end IdempotentSplitting

end IharaLemma


