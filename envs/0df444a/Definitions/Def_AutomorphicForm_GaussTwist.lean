-- Prove2me | Definitions.Def_AutomorphicForm_GaussTwist
-- name    : AutomorphicForm_GaussTwist
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/b445aff0-0262-559a-a0ca-374467edc5b9
-- title:
--   Gauss-sum twisting data for adelic GL2​ forms
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal{O}_F$, $\mathfrak{f}$ an ideal of $\mathcal{O}_F$, and $c_{\mathfrak{p}} =$ [`HeckeCharacter.idealMultiplicity F 𝔭 𝔣`](../def/HeckeCharacter_FiniteOrder.html#L18), the multiplicity of $\mathfrak{p}$ in the factorisation of $\mathfrak{f}$. The module assembles the vocabulary of a Gauss-sum combination of translates of a function on $\mathrm{GL}_2$ of the adeles. `modulusPrimes F 𝔣` is the finite set of primes dividing $\mathfrak{f}$, empty for $\mathfrak{f} = \bot$ (`mem_modulusPrimes`, `modulusPrimes_bot`). `LocalGaussFactor F 𝔣 𝔭` is the unit group of $\mathcal{O}_{\mathfrak{p}}/\mathfrak{m}_{\mathfrak{p}}^{c_{\mathfrak{p}}}$, where $\mathcal{O}_{\mathfrak{p}}$ is the valuation ring of the $\mathfrak{p}$-adic completion; `GaussIndex F 𝔣` is the product of these over $\mathfrak{p} \mid \mathfrak{f}$, carrying the product commutative group structure, and shown finite. `unitQuotLift` is a chosen set-theoretic section of the (surjective) reduction $A^{\times} \to (A/\mathfrak{m}^n)^{\times}$ for a local ring $A$; `gaussRep F 𝔣 u` applies it componentwise, lifting an index $u$ to a family of local units. `localUnif` (and `gaussUnif`) is a chosen uniformiser of the completion, of valuation $\exp(-1)$. For a family $r$ of local units, `unitIdele F 𝔣 r` is the idele with archimedean component $1$, component $r_{\mathfrak{p}}$ at each $\mathfrak{p} \mid \mathfrak{f}$ and $1$ elsewhere; `gaussUnitIdele F 𝔣 u` is this for $r =$ `gaussRep F 𝔣 u`, and `gaussWt F η 𝔣 u` is the complex number $\eta$ of that idele, for a character $\eta$ of the idele group. `gaussY F 𝔣 u` is the family with value $\tilde{u}_{\mathfrak{p}}\varpi_{\mathfrak{p}}^{-c_{\mathfrak{p}}}$ at $\mathfrak{p} \mid \mathfrak{f}$ and $0$ elsewhere; `adeleOn` turns such a family, cut off outside a finite set, into a finite adele; `finPair`/`finLift` embed a finite-adelic matrix, resp. element of $\mathrm{GL}_2$ of the finite adeles, into the adelic one with archimedean part the identity. Thus `gaussTrans F 𝔣 u` is the upper unipotent matrix $\begin{pmatrix}1 & y_u\\ 0 & 1\end{pmatrix}$ with trivial archimedean part, and $$\mathtt{gaussSumFn}\,F\,\eta\,\mathfrak{f}\,\varphi\,(g) = \sum_{u} \eta(\tilde{u})\,\varphi(g\cdot \mathtt{gaussTrans}\,F\,\mathfrak{f}\,u),$$ the sum over `GaussIndex F 𝔣` (`gaussSumFn_apply`). Two results justify the construction: if $\eta$ admits the modulus $\mathfrak{f}$, in the sense that $\eta$ kills every unit idele with trivial archimedean part all of whose finite components $u_v$ have valuation $1$ and satisfy $|u_v - 1| \le \exp(-c_v)$, then $\eta(\mathtt{unitIdele}\,r)$ depends only on the reductions of $r_{\mathfrak{p}}$ modulo $\mathfrak{m}_{\mathfrak{p}}^{c_{\mathfrak{p}}}$ (`eta_unitIdele_eq_of_mk_eq`), so that `gaussWt` can be computed from any family of local units reducing to $u$ (`gaussWt_eq_of_mk_eq`); in particular the weights do not depend on the chosen lifts. Auxiliary material, all of it private, records valuation estimates in the completions (units have valuation $1$; membership in $\mathfrak{m}^n$ forces valuation $\le \exp(-n)$, hence congruent elements differ by valuation $\le \exp(-n)$), the componentwise behaviour of `unitIdele` and its inverse, and that the combination of the constant function $1$ with trivial $\eta$ has value the cardinality of the index group, which is nonzero.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the finite adele ring, the $\mathfrak{p}$-adic completions and their valuation rings, and $\mathrm{GL}_2$ of a ring; the Gauss-sum index group, unit ideles, unipotent translates and the Gauss-sum combination defined here are the project's own.
--
--   **Where it is used.** These objects provide the automorphic-side vocabulary for twisting a form on $\mathrm{GL}_2$ of the adeles of $F$ by a finite-order Hecke character $\eta$ of modulus $\mathfrak{f}$: the twisted vector is modelled as the Gauss-sum combination of unipotent translates weighted by $\eta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GaussTwist.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain NumberField.AdelicLevel

namespace AutomorphicForm.GaussTwist

section LocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

private theorem units_map_quotient_maximalIdeal_pow_surjective (n : ℕ) :
    Function.Surjective
      (Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hsub : Subsingleton (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [hn, pow_zero, Ideal.one_eq_top])
    exact fun y => ⟨1, Subsingleton.elim _ _⟩
  · refine IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective ?_
    refine isLocalHom_of_le_jacobson_bot _ ?_
    calc (IsLocalRing.maximalIdeal A) ^ n
        ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self hn.ne'
      _ = Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

def unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : Aˣ :=
  Function.surjInv (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem unitQuotLift_spec (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom
      (unitQuotLift A n x) = x :=
  Function.surjInv_eq (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem mk_coe_unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) (unitQuotLift A n x : A)
      = ((x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
  congrArg Units.val (unitQuotLift_spec A n x)

end LocalRing

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def localUnif : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_localUnif : Valued.v (localUnif K v) = WithZero.exp (-1 : ℤ) := by
  unfold localUnif
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) :=
  Valuation.valuationSubring.integers _

private theorem valued_coe_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (integers_adicCompletionIntegers K v).one_of_isUnit hx

private theorem isUnit_of_valued_coe_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1) : IsUnit x :=
  (integers_adicCompletionIntegers K v).isUnit_of_one' hx

private theorem valued_units_coe (r : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (((r : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 :=
  valued_coe_eq_one_of_isUnit K v r.isUnit

private theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨WithZero.log γ, (WithZero.exp_log h0).symm⟩
    subst hm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.mpr (by omega)

private theorem valued_coe_le_exp_neg_one_of_mem_maximalIdeal {x : v.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  refine le_exp_neg_one_of_lt_one (lt_of_le_of_ne
    ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2) fun h => ?_)
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx))
    (isUnit_of_valued_coe_eq_one K v h)

private theorem valued_coe_le_exp_neg_of_mem_maximalIdeal_pow {n : ℕ} {x : v.adicCompletionIntegers K}
    (hx : x ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      ≤ WithZero.exp (-(n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  | succ n ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun m hm y hy => ?_) (fun y z hy hz => ?_)
      · rw [show ((m * y : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (m : v.adicCompletion K) * y from rfl, map_mul, Nat.cast_succ, neg_add,
          WithZero.exp_add]
        exact mul_le_mul' (ih hm) (valued_coe_le_exp_neg_one_of_mem_maximalIdeal K v hy)
      · rw [show ((y + z : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (y : v.adicCompletion K) + z from rfl]
        exact Valuation.map_add_le _ hy hz

private theorem valued_coe_sub_le_of_mk_eq {n : ℕ} {x y : v.adicCompletionIntegers K}
    (h : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) x
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) y) :
    Valued.v ((x : v.adicCompletion K) - y) ≤ WithZero.exp (-(n : ℤ)) := by
  have h' := valued_coe_le_exp_neg_of_mem_maximalIdeal_pow K v (Ideal.Quotient.eq.mp h)
  rwa [AddSubgroupClass.coe_sub] at h'

end Local

section Adelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def adeleOn (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨fun w => if w ∈ S then y w else 0,
    S.eventually_cofinite_notMem.mono fun w hw => by
      dsimp only
      rw [if_neg hw]
      exact (w.adicCompletionIntegers K).zero_mem⟩

private theorem adeleOn_apply (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) (w : HeightOneSpectrum R) :
    adeleOn S y w = if w ∈ S then y w else 0 := rfl

private theorem adeleOn_apply_of_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) {w : HeightOneSpectrum R} (hw : w ∈ S) :
    adeleOn S y w = y w := by
  rw [adeleOn_apply, if_pos hw]

private theorem adeleOn_apply_of_not_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ∉ S) : adeleOn S y w = 0 := by
  rw [adeleOn_apply, if_neg hw]

private theorem matrix_eq_of_parts {M M' : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (ha : (adeleArch R K).mapMatrix M = (adeleArch R K).mapMatrix M')
    (hf : (adeleFin R K).mapMatrix M = (adeleFin R K).mapMatrix M') : M = M' := by
  ext i j
  exact Prod.ext (congrFun (congrFun ha i) j) (congrFun (congrFun hf i) j)

def finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j =>
    (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, m i j) : AdeleRing R K)

private theorem mapMatrix_adeleArch_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleArch R K).mapMatrix (finPair m) = 1 := by
  ext i j
  rfl

private theorem mapMatrix_adeleFin_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleFin R K).mapMatrix (finPair m) = m := by
  ext i j
  rfl

private theorem finPair_one : finPair (R := R) (K := K) 1 = 1 :=
  matrix_eq_of_parts (by rw [mapMatrix_adeleArch_finPair, map_one])
    (by rw [mapMatrix_adeleFin_finPair, map_one])

private theorem finPair_mul (m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finPair m * finPair m' = finPair (m * m') :=
  matrix_eq_of_parts
    (by rw [map_mul, mapMatrix_adeleArch_finPair, mapMatrix_adeleArch_finPair,
      mapMatrix_adeleArch_finPair, mul_one])
    (by rw [map_mul, mapMatrix_adeleFin_finPair, mapMatrix_adeleFin_finPair,
      mapMatrix_adeleFin_finPair])

def finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (AdeleRing R K) where
  val := finPair (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  inv := finPair
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  val_inv := by rw [finPair_mul, Units.mul_inv, finPair_one]
  inv_val := by rw [finPair_mul, Units.inv_mul, finPair_one]

private theorem glArch_finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : glArch R K (finLift g) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

private theorem glFin_finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : glFin R K (finLift g) = g := by
  ext i j
  rfl

private theorem coe_prod_apply_of_units {ι : Type*} (s : Finset ι)
    (f : ι → (FiniteAdeleRing R K)ˣ) (w : HeightOneSpectrum R) :
    ((∏ i ∈ s, f i : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w
      = ∏ i ∈ s, (((f i : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) w) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [coe_one_apply]
  | cons a s ha ih => simp only [Finset.prod_cons, Units.val_mul, coe_mul_apply, ih]

end Adelic

section Gauss

variable (F : Type) [Field F] [NumberField F]

open scoped Classical

def modulusPrimes (𝔣 : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : 𝔣 = ⊥ then ∅ else (Ideal.finite_factors (fun h' => h h')).toFinset

theorem mem_modulusPrimes {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ modulusPrimes F 𝔣 ↔ v.asIdeal ∣ 𝔣 := by
  rw [modulusPrimes, dif_neg h𝔣, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem modulusPrimes_bot : modulusPrimes F ⊥ = ∅ := by
  rw [modulusPrimes, dif_pos rfl]

abbrev LocalGaussFactor (𝔣 : Ideal (𝓞 F)) (𝔭 : HeightOneSpectrum (𝓞 F)) : Type :=
  ((𝔭.adicCompletionIntegers F) ⧸
    (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F))
      ^ (HeckeCharacter.idealMultiplicity F 𝔭 𝔣))ˣ

def GaussIndex (𝔣 : Ideal (𝓞 F)) : Type :=
  ∀ 𝔭 : modulusPrimes F 𝔣, LocalGaussFactor F 𝔣 𝔭.1

instance (𝔣 : Ideal (𝓞 F)) : CommGroup (GaussIndex F 𝔣) := Pi.commGroup

instance (𝔣 : Ideal (𝓞 F)) (𝔭 : modulusPrimes F 𝔣) : Finite (LocalGaussFactor F 𝔣 𝔭.1) := by
  have : Finite ((𝔭.1.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
        ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣)) :=
    IsLocalRing.isOpen_iff_finite_quotient.mp
      (IsLocalRing.isOpen_maximalIdeal_pow (𝔭.1.adicCompletionIntegers F) _)
  exact instFiniteUnits

instance (𝔣 : Ideal (𝓞 F)) : Fintype (GaussIndex F 𝔣) := by
  have : Finite (GaussIndex F 𝔣) := Pi.finite
  exact Fintype.ofFinite _

noncomputable def gaussRep (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    (𝔭 : modulusPrimes F 𝔣) : (𝔭.1.adicCompletionIntegers F)ˣ :=
  unitQuotLift (𝔭.1.adicCompletionIntegers F)
    (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣) (u 𝔭)

private theorem mk_coe_gaussRep (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) (𝔭 : modulusPrimes F 𝔣) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
        ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
      ((gaussRep F 𝔣 u 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)
    = ((u 𝔭 : LocalGaussFactor F 𝔣 𝔭.1) : 𝔭.1.adicCompletionIntegers F
        ⧸ (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣)) :=
  mk_coe_unitQuotLift _ _ (u 𝔭)

noncomputable def gaussUnif (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭.adicCompletion F :=
  localUnif F 𝔭

noncomputable def gaussY (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭.adicCompletion F :=
  if h : 𝔭 ∈ modulusPrimes F 𝔣 then
    ((gaussRep F 𝔣 u ⟨𝔭, h⟩ : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F)
      * (gaussUnif F 𝔭)⁻¹ ^ (HeckeCharacter.idealMultiplicity F 𝔭 𝔣)
  else 0

def unitIdele (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (∏ 𝔭 : modulusPrimes F 𝔣, localUnit (𝓞 F) F 𝔭.1
    ⟨(r 𝔭 : 𝔭.1.adicCompletionIntegers F), (r 𝔭)⁻¹, by simp, by simp⟩)

def gaussUnitIdele (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (∏ 𝔭 : modulusPrimes F 𝔣, localUnit (𝓞 F) F 𝔭.1
    ⟨(gaussRep F 𝔣 u 𝔭 : 𝔭.1.adicCompletionIntegers F),
     (gaussRep F 𝔣 u 𝔭)⁻¹, by simp, by simp⟩)

private theorem gaussUnitIdele_eq (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) :
    gaussUnitIdele F 𝔣 u = unitIdele F 𝔣 (gaussRep F 𝔣 u) := rfl

def gaussWt (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : ℂ :=
  ((η (gaussUnitIdele F 𝔣 u) : ℂˣ) : ℂ)

def gaussTrans (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) : AdelicGL2 (𝓞 F) F :=
  finLift (unipotentGL2 (adeleOn (modulusPrimes F 𝔣) (gaussY F 𝔣 u)))

def gaussSumFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u)

theorem gaussSumFn_apply (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    gaussSumFn F η 𝔣 φ g = ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u) :=
  rfl

private theorem unitIdele_fst (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [unitIdele, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem unitIdele_inv_fst (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [unitIdele, ← map_inv, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem unitIdele_snd_apply_of_not_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ modulusPrimes F 𝔣) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [unitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  exact Finset.prod_eq_one fun 𝔭 _ =>
    localUnit_apply_of_ne (𝓞 F) F 𝔭.1 _ (fun h => hw (h ▸ 𝔭.2))

private theorem unitIdele_snd_apply_of_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = (((r ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) := by
  rw [unitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  refine (Finset.prod_eq_single (⟨𝔭, h𝔭⟩ : modulusPrimes F 𝔣)
    (fun 𝔮 _ h𝔮 => localUnit_apply_of_ne (𝓞 F) F 𝔮.1 _ ?_)
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · exact fun h => h𝔮 (Subtype.ext h.symm)
  · exact localUnit_apply_self (𝓞 F) F 𝔭 _

private theorem valued_unitIdele_snd_apply (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) = 1 := by
  by_cases hw : w ∈ modulusPrimes F 𝔣
  · rw [unitIdele_snd_apply_of_mem F 𝔣 r hw]
    exact valued_units_coe F w (r ⟨w, hw⟩)
  · rw [unitIdele_snd_apply_of_not_mem F 𝔣 r hw]; exact map_one _

private theorem inv_snd_apply_mul_snd_apply (x : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (x : AdeleRing (𝓞 F) F).2 w = 1 := by
  have h : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (x : AdeleRing (𝓞 F) F) = 1 :=
    x.inv_mul
  calc ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (x : AdeleRing (𝓞 F) F).2 w
      = (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (x : AdeleRing (𝓞 F) F)).2 w := rfl
    _ = (1 : AdeleRing (𝓞 F) F).2 w := by rw [h]
    _ = 1 := rfl

private theorem valued_unitIdele_inv_snd_apply (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) = 1 := by
  have h := congrArg Valued.v (inv_snd_apply_mul_snd_apply F (unitIdele F 𝔣 r) w)
  rwa [map_mul, valued_unitIdele_snd_apply, mul_one, map_one] at h

private theorem unitIdele_inv_snd_apply_of_not_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ modulusPrimes F 𝔣) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  have h := inv_snd_apply_mul_snd_apply F (unitIdele F 𝔣 r) w
  rwa [unitIdele_snd_apply_of_not_mem F 𝔣 r hw, mul_one] at h

private theorem unitIdele_inv_snd_apply_of_mem (𝔣 : Ideal (𝓞 F))
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    (((unitIdele F 𝔣 r)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = ((((r ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F))⁻¹ := by
  have h := inv_snd_apply_mul_snd_apply F (unitIdele F 𝔣 r) 𝔭
  rw [unitIdele_snd_apply_of_mem F 𝔣 r h𝔭] at h
  exact eq_inv_of_mul_eq_one_left h

theorem eta_unitIdele_eq_of_mk_eq (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {r r' : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ}
    (h : ∀ 𝔭 : modulusPrimes F 𝔣,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
        ((r 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
        ((r' 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)) :
    η (unitIdele F 𝔣 r) = η (unitIdele F 𝔣 r') := by

  have hsnd : ∀ w : HeightOneSpectrum (𝓞 F),
      ((unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
        = ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
          * (((unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w :=
    fun _ => rfl
  have harch : ((unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
      : AdeleRing (𝓞 F) F).1 = 1 := by
    have e : ((unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
          : AdeleRing (𝓞 F) F).1
        = ((unitIdele F 𝔣 r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
          * (((unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := rfl
    rw [e, unitIdele_fst, unitIdele_inv_fst, mul_one]
  have hunit : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (((unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
        : AdeleRing (𝓞 F) F).2 w) = 1 := fun w => by
    rw [hsnd, map_mul, valued_unitIdele_snd_apply, valued_unitIdele_inv_snd_apply, mul_one]
  have hcong : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (((unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
          : AdeleRing (𝓞 F) F).2 w - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) := fun w => by
    rw [hsnd]
    by_cases hw : w ∈ modulusPrimes F 𝔣
    · rw [unitIdele_snd_apply_of_mem F 𝔣 r hw, unitIdele_inv_snd_apply_of_mem F 𝔣 r' hw]
      have hy : Valued.v (((r' ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ)
          : w.adicCompletionIntegers F) : w.adicCompletion F) = 1 := valued_units_coe F w _
      have hy0 : (((r' ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ)
          : w.adicCompletionIntegers F) : w.adicCompletion F) ≠ 0 :=
        (Valuation.ne_zero_iff _).mp (by rw [hy]; exact one_ne_zero)
      rw [show (((r ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
            : w.adicCompletion F)
          * ((((r' ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
            : w.adicCompletion F))⁻¹ - 1
        = ((((r ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
            : w.adicCompletion F)
          - (((r' ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
            : w.adicCompletion F))
          * ((((r' ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
            : w.adicCompletion F))⁻¹ from by rw [sub_mul, mul_inv_cancel₀ hy0],
        map_mul, map_inv₀, hy, inv_one, mul_one]
      exact valued_coe_sub_le_of_mk_eq F w (h ⟨w, hw⟩)
    · rw [unitIdele_snd_apply_of_not_mem F 𝔣 r hw, unitIdele_inv_snd_apply_of_not_mem F 𝔣 r' hw,
        mul_one, sub_self, map_zero]
      exact zero_le'
  have hη : η (unitIdele F 𝔣 r * (unitIdele F 𝔣 r')⁻¹) = 1 :=
    hmod _ harch fun w => ⟨hunit w, hcong w⟩
  rwa [map_mul, map_inv, mul_inv_eq_one] at hη

theorem gaussWt_eq_of_mk_eq (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) (u : GaussIndex F 𝔣)
    (r : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ)
    (hr : ∀ 𝔭 : modulusPrimes F 𝔣,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
        ((r 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)
      = ((u 𝔭 : LocalGaussFactor F 𝔣 𝔭.1) : 𝔭.1.adicCompletionIntegers F
          ⧸ (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
            ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))) :
    gaussWt F η 𝔣 u = ((η (unitIdele F 𝔣 r) : ℂˣ) : ℂ) := by
  unfold gaussWt
  rw [gaussUnitIdele_eq]
  congr 1
  exact eta_unitIdele_eq_of_mk_eq F η 𝔣 hmod fun 𝔭 => (mk_coe_gaussRep F 𝔣 u 𝔭).trans (hr 𝔭).symm

private theorem gaussSumFn_one_const (𝔣 : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    gaussSumFn F 1 𝔣 (fun _ => 1) g = (Fintype.card (GaussIndex F 𝔣) : ℂ) := by
  simp [gaussSumFn, gaussWt]

private theorem gaussSumFn_one_const_ne_zero (𝔣 : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    gaussSumFn F 1 𝔣 (fun _ => 1) g ≠ 0 := by
  haveI : Nonempty (GaussIndex F 𝔣) := ⟨1⟩
  rw [gaussSumFn_one_const]
  exact_mod_cast Fintype.card_ne_zero

end Gauss

end AutomorphicForm.GaussTwist


