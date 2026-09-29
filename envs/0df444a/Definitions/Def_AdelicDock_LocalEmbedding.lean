-- Prove2me | Definitions.Def_AdelicDock_LocalEmbedding
-- name    : AdelicDock_LocalEmbedding
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/1c9c3134-a913-5e75-a7dd-33d61297bd6f
-- title:
--   Local-to-adelic embeddings of GL2​ and local level structures
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$ and $v$ a height-one prime of $R$. The function `splice R K v a t` modifies a finite adele $a$ by replacing its $v$-component by $t \in K_v$ (still a finite adele, since the integrality condition away from $v$ is untouched), and `localMat R K v g`, for $g \in M_2(K_v)$, is the matrix of finite adeles whose $(i,j)$ entry is the identity matrix's entry spliced at $v$ with $g_{ij}$: it equals $g$ at $v$ and the identity matrix at every other place. Since this is multiplicative and unital, it yields the group homomorphism `localEmbed R K v` : $GL_2(K_v) \to GL_2(\mathbb{A}_{f,K})$, injective, with $v$-component $g$ and all other components $1$ (measured by `AdelicLevel.finComponent`). Similarly `finMat` places a finite adelic matrix in the finite slot and the identity in the archimedean slot, giving `finEmbed R K` : $GL_2(\mathbb{A}_{f,K}) \to GL_2(\mathbb{A}_K)$, injective, whose finite part is the given element and whose archimedean part is $1$; consequently membership in `AdelicLevel.levelOne` (resp. `levelZero`) of an image is equivalent to membership in `AdelicLevel.finiteLevelOne` (resp. `finiteLevelZero`).
--
--   `localLevelOne R K v N` is the pullback of `AdelicLevel.finiteLevelOne R K N` along `localEmbed`. The structure `IsLocalLevelOne R K v N m` records, as three fields, that all entries of $m$ lie in $\mathcal{O}_v$, that $\mathrm{v}(m_{10}) \le$ `AdelicLevel.idealBound R N v` and that $\mathrm{v}(m_{11}-1) \le$ the same bound (the bound being $0$ for $N = \bot$ and $\exp(-\operatorname{ord}_v N)$ otherwise); `isLevelOneMatrix_localMat_iff` identifies this with the adelic level-one condition for `localMat`, and `mem_localLevelOne_iff` then describes `localLevelOne` by imposing `IsLocalLevelOne` on an element and on its inverse.
--
--   Over $\mathbb{Q}$, for a prime $p$: [`padicPlace p`](../def/GaloisRep_CompletionBridge.html#L25) is the corresponding height-one prime of $\mathcal{O}_{\mathbb{Q}}$, `padicRingEquiv p` the ring isomorphism $\mathbb{Q}_p \cong$ its adic completion, `padicGL p` the induced map on $GL_2$, and `padicToFinAdelic p`, `padicToAdelic p` its composites with `localEmbed` and `finEmbed`; all are injective. A valuation dictionary (`norm_le_one_iff_mem`, `valued_le_valued_iff`, `idealBound_ratLevel`, `norm_natCast_eq_zpow_neg_factorization`, `valued_coe_le_idealBound_iff`) compares $p$-adic absolute values with the valuation on the completion, for the level ideal `ratLevel N = (N)`. The final results state that for $N \neq 0$ and $n \ge \operatorname{ord}_p N$, every $k \in$ [`LocalNewvector.padicK1 p n`](../def/LocalNewvector_CongruenceSubgroupK1.html#L161) has $\mathrm{padicToAdelic}\,p\,k$ in `AdelicLevel.levelOne (𝓞 ℚ) ℚ (ratLevel N)`, and the image subgroup of `padicK1 p n` is contained in that adelic level subgroup.
--
--   **Relation to Mathlib.** Mathlib supplies the finite and full adele rings, adic completions and the identification $\mathbb{Q}_p \cong \mathbb{Q}_{(p)}^{\wedge}$ (`Padic.adicCompletionEquiv`), together with `Matrix.GeneralLinearGroup.map`; the place-by-place embeddings of $GL_2(K_v)$ and $GL_2(\mathbb{A}_{f,K})$ into $GL_2(\mathbb{A}_K)$, and the local level predicate `IsLocalLevelOne`, are the project's own.
--
--   **Where it is used.** These embeddings and the compatibility of $p$-adic congruence subgroups with adelic level structures are what allows local data at $p$ to be fed into the adelic description of modular forms of level $N$ on $GL_2$ over $\mathbb{Q}$, and in particular the transport of the local group $K_1(p^n)$ into the adelic level-$N$ subgroup used on the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AdelicDock_LocalEmbedding.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrix_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] at hw
  rw [hw]

theorem matrix_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

open scoped Classical in

def splice (a : FiniteAdeleRing R K) (t : v.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨Function.update (⇑a) v t, (Filter.eventually_cofinite_ne v).mp (a.2.mono fun w hw hne => by
    rw [Function.update_of_ne hne]; exact hw)⟩

open scoped Classical in
@[simp] theorem splice_apply_self (a : FiniteAdeleRing R K) (t : v.adicCompletion K) :
    splice R K v a t v = t := by
  show Function.update (⇑a) v t v = t
  simp

open scoped Classical in
theorem splice_apply_of_ne (a : FiniteAdeleRing R K) (t : v.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : splice R K v a t w = a w := by
  show Function.update (⇑a) v t w = a w
  simp [Function.update_of_ne hw]

def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) (g i j)

theorem localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    localMat R K v g i j v = g i j := by
  simp [localMat]

theorem localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat R K v g i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  simp only [localMat, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat_apply_self]

theorem mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMat_apply_of_ne R K v g i j hw]

theorem localMat_one : localMat R K v 1 = 1 := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat_self, map_one]
  · rw [mapMatrix_localMat_of_ne R K v _ hw, map_one]

theorem localMat_mul (g h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    localMat R K v (g * h) = localMat R K v g * localMat R K v h := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, mapMatrix_localMat_self, mapMatrix_localMat_self, mapMatrix_localMat_self]
  · rw [map_mul, mapMatrix_localMat_of_ne R K v _ hw, mapMatrix_localMat_of_ne R K v _ hw,
      mapMatrix_localMat_of_ne R K v _ hw, mul_one]

def localEmbed : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat R K v g
      inv := localMat R K v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat_mul, Units.mul_inv, localMat_one]
      inv_val := by rw [← localMat_mul, Units.inv_mul, localMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMat_one R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMat_mul R K v _ _)

@[simp] theorem coe_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    ((localEmbed R K v g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) = localMat R K v g := rfl

theorem finComponent_localEmbed_self (g : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.finComponent R K v (localEmbed R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_self]

theorem finComponent_localEmbed_of_ne (g : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : AdelicLevel.finComponent R K w (localEmbed R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.finComponent_apply, coe_localEmbed, localMat_apply_of_ne R K v _ i j hw, Units.val_one]

theorem localEmbed_injective : Function.Injective (localEmbed R K v) := fun g h hgh => by
  rw [← finComponent_localEmbed_self R K v g, ← finComponent_localEmbed_self R K v h, hgh]

def finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMat R K g) = 1 := by
  ext i j
  simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_finMat (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMat R K g) = g := by
  ext i j
  simp [finMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem finMat_one : finMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat, map_one])
    (by rw [mapMatrix_fin_finMat, map_one])

theorem finMat_mul (g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finMat R K (g * h) = finMat R K g * finMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, mapMatrix_fin_finMat])

def finEmbed : GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := finMat R K g
      inv := finMat R K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMat_mul, Units.mul_inv, finMat_one]
      inv_val := by rw [← finMat_mul, Units.inv_mul, finMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMat_mul R K _ _)

@[simp] theorem coe_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((finEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = finMat R K g := rfl

theorem glFin_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glFin R K (finEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glFin_apply, coe_finEmbed]
  rfl

theorem glArch_finEmbed (g : GL (Fin 2) (FiniteAdeleRing R K)) : AdelicLevel.glArch R K (finEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, coe_finEmbed, Units.val_one]
  rfl

theorem finEmbed_injective : Function.Injective (finEmbed R K) := fun g h hgh => by
  rw [← glFin_finEmbed R K g, ← glFin_finEmbed R K h, hgh]

theorem finEmbed_mem_levelOne_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelOne R K N ↔ g ∈ AdelicLevel.finiteLevelOne R K N := by
  rw [AdelicLevel.mem_levelOne_iff, glFin_finEmbed]

theorem finEmbed_mem_levelZero_iff {N : Ideal R} (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    finEmbed R K g ∈ AdelicLevel.levelZero R K N ↔ g ∈ AdelicLevel.finiteLevelZero R K N := by
  rw [AdelicLevel.mem_levelZero_iff, glFin_finEmbed]

def localLevelOne (N : Ideal R) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  (AdelicLevel.finiteLevelOne R K N).comap (localEmbed R K v)

theorem localEmbed_mem_finiteLevelOne_iff {N : Ideal R} (k : GL (Fin 2) (v.adicCompletion K)) :
    localEmbed R K v k ∈ AdelicLevel.finiteLevelOne R K N ↔ k ∈ localLevelOne R K v N :=
  Iff.rfl

structure IsLocalLevelOne (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop where
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  lowerLeft : Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v
  lowerRight : Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v

theorem isLevelOneMatrix_localMat_iff {N : Ideal R} (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.IsLevelOneMatrix R K N (localMat R K v m) ↔ IsLocalLevelOne R K v N m := by
  constructor
  · rintro ⟨⟨hint, hll⟩, hlr⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := hint i j v
      rwa [localMat_apply_self] at this
    · have := hll v
      rwa [localMat_apply_self] at this
    · have := hlr v
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_self] at this
  · rintro ⟨hint, hll, hlr⟩
    refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hint i j
      · rw [localMat_apply_of_ne R K v m i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hll
      · rw [localMat_apply_of_ne R K v m 1 0 hw, Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le'
    · by_cases hw : w = v
      · subst hw; rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_self]; exact hlr
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply, localMat_apply_of_ne R K v m 1 1 hw,
          Matrix.one_apply_eq, sub_self, map_zero]
        exact zero_le'

theorem mem_localLevelOne_iff {N : Ideal R} (k : GL (Fin 2) (v.adicCompletion K)) :
    k ∈ localLevelOne R K v N ↔
      IsLocalLevelOne R K v N k ∧ IsLocalLevelOne R K v N ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _) := by
  rw [localLevelOne, Subgroup.mem_comap, AdelicLevel.mem_finiteLevelOne_iff, ← map_inv, coe_localEmbed,
    coe_localEmbed, isLevelOneMatrix_localMat_iff, isLevelOneMatrix_localMat_iff]

end Generic

section Rat

variable (p : ℕ) [Fact p.Prime]

def padicPlace : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩

def padicRingEquiv : ℚ_[p] ≃+* (padicPlace p).adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toRingEquiv

theorem padicRingEquiv_apply (x : ℚ_[p]) :
    padicRingEquiv p x = Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, Fact.out⟩ x := rfl

def padicGL : GL (Fin 2) ℚ_[p] →* GL (Fin 2) ((padicPlace p).adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.map (padicRingEquiv p).toRingHom

theorem padicGL_apply (k : GL (Fin 2) ℚ_[p]) (i j : Fin 2) :
    (padicGL p k : Matrix _ _ _) i j = padicRingEquiv p ((k : Matrix _ _ _) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j k

theorem padicGL_injective : Function.Injective (padicGL p) := fun g h hgh => by
  refine Matrix.GeneralLinearGroup.ext fun i j => (padicRingEquiv p).injective ?_
  rw [← padicGL_apply, ← padicGL_apply, hgh]

def padicToFinAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (localEmbed (𝓞 ℚ) ℚ (padicPlace p)).comp (padicGL p)

def padicToAdelic : GL (Fin 2) ℚ_[p] →* GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  (finEmbed (𝓞 ℚ) ℚ).comp (padicToFinAdelic p)

theorem padicToFinAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToFinAdelic p k = localEmbed (𝓞 ℚ) ℚ (padicPlace p) (padicGL p k) := rfl

theorem padicToAdelic_apply (k : GL (Fin 2) ℚ_[p]) :
    padicToAdelic p k = finEmbed (𝓞 ℚ) ℚ (padicToFinAdelic p k) := rfl

theorem finComponent_padicToFinAdelic_self (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) (padicToFinAdelic p k) = padicGL p k :=
  finComponent_localEmbed_self _ _ _ _

theorem finComponent_padicToFinAdelic_of_ne (k : GL (Fin 2) ℚ_[p]) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ padicPlace p) : AdelicLevel.finComponent (𝓞 ℚ) ℚ w (padicToFinAdelic p k) = 1 :=
  finComponent_localEmbed_of_ne _ _ _ _ hw

theorem glFin_padicToAdelic (k : GL (Fin 2) ℚ_[p]) :
    AdelicLevel.glFin (𝓞 ℚ) ℚ (padicToAdelic p k) = padicToFinAdelic p k :=
  glFin_finEmbed _ _ _

theorem glArch_padicToAdelic (k : GL (Fin 2) ℚ_[p]) : AdelicLevel.glArch (𝓞 ℚ) ℚ (padicToAdelic p k) = 1 :=
  glArch_finEmbed _ _ _

theorem padicToAdelic_injective : Function.Injective (padicToAdelic p) :=
  (finEmbed_injective _ _).comp ((localEmbed_injective _ _ _).comp (padicGL_injective p))

theorem padicRingEquiv_coe_mem (x : ℤ_[p]) :
    padicRingEquiv p (x : ℚ_[p]) ∈ (padicPlace p).adicCompletionIntegers ℚ := by
  rw [padicRingEquiv_apply, ← PadicInt.coe_adicCompletionIntegersEquiv_apply]
  exact SetLike.coe_mem _

theorem norm_le_one_iff_mem (y : ℚ_[p]) :
    ‖y‖ ≤ 1 ↔ padicRingEquiv p y ∈ (padicPlace p).adicCompletionIntegers ℚ := by
  refine ⟨fun hy => padicRingEquiv_coe_mem p ⟨y, hy⟩, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).surjective ⟨_, hy⟩
  have hx' : padicRingEquiv p (x : ℚ_[p]) = padicRingEquiv p y := by
    rw [padicRingEquiv_apply, ← PadicInt.coe_adicCompletionIntegersEquiv_apply, hx]
  rw [← (padicRingEquiv p).injective hx']
  exact x.norm_le_one

theorem valued_le_valued_iff (x y : ℚ_[p]) (hy : y ≠ 0) :
    Valued.v (padicRingEquiv p x) ≤ Valued.v (padicRingEquiv p y) ↔ ‖x‖ ≤ ‖y‖ := by
  have hy' : padicRingEquiv p y ≠ 0 := (map_ne_zero (padicRingEquiv p)).mpr hy
  have hv : 0 < Valued.v (padicRingEquiv p y) := (Valuation.pos_iff _).mpr hy'
  rw [← div_le_one₀ hv, ← Valuation.map_div, ← map_div₀,
    ← HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (padicPlace p), ← norm_le_one_iff_mem,
    norm_div, div_le_one (norm_pos_iff.mpr hy)]

def ratLevel (N : ℕ) : Ideal (𝓞 ℚ) := Ideal.span {(N : 𝓞 ℚ)}

theorem ratLevel_ne_bot {N : ℕ} (hN : N ≠ 0) : ratLevel N ≠ ⊥ := by
  rw [ratLevel, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hN

theorem ratLevel_one : ratLevel 1 = ⊤ := by
  rw [ratLevel, Nat.cast_one, Ideal.span_singleton_one]

theorem idealBound_ratLevel {N : ℕ} (hN : N ≠ 0) :
    AdelicLevel.idealBound (𝓞 ℚ) (ratLevel N) (padicPlace p) = Valued.v (padicRingEquiv p (N : ℚ_[p])) := by
  have hN' : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN
  rw [AdelicLevel.idealBound_of_ne_bot (ratLevel_ne_bot hN), ratLevel,
    ← HeightOneSpectrum.intValuation_if_neg _ hN', ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation, map_natCast]
  congr 1
  exact map_natCast (algebraMap (𝓞 ℚ) ((padicPlace p).adicCompletion ℚ)) N

theorem norm_natCast_eq_zpow_neg_factorization {N : ℕ} (hN : N ≠ 0) :
    ‖(N : ℚ_[p])‖ = (p : ℝ) ^ (-(N.factorization p : ℤ)) := by
  rw [Nat.factorization_def N (Fact.out : p.Prime), Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN),
    Padic.valuation_natCast]

theorem valued_coe_le_idealBound_iff {N : ℕ} (hN : N ≠ 0) (x : ℤ_[p]) :
    Valued.v (padicRingEquiv p (x : ℚ_[p])) ≤ AdelicLevel.idealBound (𝓞 ℚ) (ratLevel N) (padicPlace p) ↔
      x ∈ Ideal.span {(p : ℤ_[p]) ^ N.factorization p} := by
  rw [idealBound_ratLevel p hN, valued_le_valued_iff p _ _ (by exact_mod_cast hN),
    norm_natCast_eq_zpow_neg_factorization p hN, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rfl

theorem isLocalLevelOne_padicGL {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : N.factorization p ≤ n)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ LocalNewvector.padicK1 p n) :
    IsLocalLevelOne (𝓞 ℚ) ℚ (padicPlace p) (ratLevel N) (padicGL p k : Matrix _ _ _) := by
  obtain ⟨y, rfl, hc, hd⟩ := hk
  have hpow : Ideal.span {(p : ℤ_[p]) ^ n} ≤ Ideal.span {(p : ℤ_[p]) ^ N.factorization p} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hn)
  have hentry : ∀ i j : Fin 2,
      ((padicGL p (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) y) :
          GL (Fin 2) ((padicPlace p).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) ((padicPlace p).adicCompletion ℚ)) i j
        = padicRingEquiv p (((y : Matrix (Fin 2) (Fin 2) ℤ_[p]) i j : ℤ_[p]) : ℚ_[p]) := fun i j => by
    rw [padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [hentry]; exact padicRingEquiv_coe_mem p _
  · rw [hentry, valued_coe_le_idealBound_iff p hN]; exact hpow hc
  · rw [hentry, ← map_one (padicRingEquiv p), ← map_sub, ← PadicInt.coe_one, ← PadicInt.coe_sub,
      valued_coe_le_idealBound_iff p hN]
    exact hpow hd

theorem padicGL_mem_localLevelOne {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : N.factorization p ≤ n)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ LocalNewvector.padicK1 p n) :
    padicGL p k ∈ localLevelOne (𝓞 ℚ) ℚ (padicPlace p) (ratLevel N) := by
  rw [mem_localLevelOne_iff, ← map_inv]
  exact ⟨isLocalLevelOne_padicGL p hN hn hk, isLocalLevelOne_padicGL p hN hn (inv_mem hk)⟩

theorem padicToAdelic_mem_levelOne {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : N.factorization p ≤ n)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ LocalNewvector.padicK1 p n) :
    padicToAdelic p k ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [padicToAdelic_apply, finEmbed_mem_levelOne_iff, padicToFinAdelic_apply, localEmbed_mem_finiteLevelOne_iff]
  exact padicGL_mem_localLevelOne p hN hn hk

theorem map_padicK1_le_levelOne {N : ℕ} (hN : N ≠ 0) {n : ℕ} (hn : N.factorization p ≤ n) :
    (LocalNewvector.padicK1 p n).map (padicToAdelic p) ≤ AdelicLevel.levelOne (𝓞 ℚ) ℚ (ratLevel N) := by
  rintro _ ⟨k, hk, rfl⟩
  exact padicToAdelic_mem_levelOne p hN hn hk

end Rat

end AdelicDock

end


