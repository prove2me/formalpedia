-- Prove2me | Definitions.Def_OAIQWKAP002
-- name    : OAIQWKAP002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:42:37.398197+00:00
-- url     : https://prove2.me/theorems/523f7c47-4294-4eb4-903d-3f0666c54fc3
-- title:
--   OpenAI Kaplansky direct-finiteness counterexample (characteristic two) split: the prescribed counterexample
-- statement:
--   The last definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyCounterexample.finitelyPresented_counterexample`. It holds OpenAI's definitions of the prescribed counterexample. The finite search fixes the outer input `selectedH`, `selectedInput` and the first successful pair `selectedPair`. From these, namespace `OAI.KaplanskyCounterexample.Prescription.Output` defines the coefficient field `Coeff` (a finite field of characteristic two), the group `G`, and the two elements `a` and `b` of the group algebra `MonoidAlgebra Coeff G` with $ab = 1 \ne ba$. The bundle also contains the lemmas these definitions use in their bodies. It is ported to Lean 4.33.1 and Mathlib 0df444a from the modules `FiniteParameters`, `LexicographicOrder`, `OddTorsion`, `ParameterBounds`, `PrescribedData`, `PrescribedDirections`, `PrescribedFields`, `PrescribedIncidence`, `PrescribedOutputs`, `PrescribedParameters`, `PrescribedSearch`, `PrescribedSlots`, `QuotientField` and `SimplexBound` of `lean/OAI/RingTheory/DirectFiniteness` (OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, OpenAI Math Release, September 23, 2026, result family 197, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0).
--
--   It imports the bundles `OAIQWKAP000` and `OAIQWKAP001`.
-- source:
--   OpenAI, A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 197; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/DirectFiniteness at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWKAP000
import Definitions.Def_OAIQWKAP001

section
-- module Solutions.OAIQW_Kaplansky.FiniteParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

lemma source_prime_exists : ∃ p : ℕ, p.Prime ∧ sourceQ^100 ∣ p+1 := by
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one]
    rw [Nat.mul_comm]
  refine ⟨2*sourceQ^100-1,(by rw [hp]; exact mersenne_21701_prime),?_⟩
  have hpos : 0 < sourceQ^100 := pow_pos sourceQ_pos _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*sourceQ^100)]
  exact dvd_mul_left _ _

attribute [local instance] OAI.KaplanskyCounterexample.FiniteGeometry.instDecidablePredNatAndPrimeDvdHPowSourceQOfNatHAdd
def sourcePrime : ℕ := Nat.find source_prime_exists

def sourceD : ℕ := sourcePrime+1

lemma sourcePrime_prime : sourcePrime.Prime := (Nat.find_spec source_prime_exists).1
lemma sourcePrime_le (p : ℕ) (hp : p.Prime) (hc : sourceQ^100 ∣ p+1) : sourcePrime ≤ p :=
  Nat.find_min' source_prime_exists ⟨hp,hc⟩
lemma sourceD_divisible : sourceQ^100 ∣ sourceD := (Nat.find_spec source_prime_exists).2

lemma sourceD_bounds : sourceQ^100 ≤ sourceD ∧ sourceD ≤ 2*sourceQ^100 := by
  refine ⟨Nat.le_of_dvd (by unfold sourceD; omega) sourceD_divisible,?_⟩
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one,Nat.mul_comm]
  have hd : sourceQ^100 ∣ (2*sourceQ^100-1)+1 := by
    rw [Nat.sub_add_cancel (by have := pow_pos sourceQ_pos 100; omega)]
    exact dvd_mul_left _ _
  have hb : sourcePrime ≤ 2*sourceQ^100-1 := Nat.find_min' source_prime_exists ⟨(by rw [hp]; exact mersenne_21701_prime),hd⟩
  unfold sourceD
  have := pow_pos sourceQ_pos 100
  omega

lemma sourceD_q_dvd : sourceQ ∣ sourceD :=
  (dvd_pow_self sourceQ (by decide : 100 ≠ 0)).trans sourceD_divisible

lemma sourceD_log : Nat.log sourceQ sourceD = 100 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact sourceD_bounds.1
  · calc
      sourceD ≤ 2*sourceQ^100 := sourceD_bounds.2
      _ < sourceQ^100*sourceQ := by
        rw [Nat.mul_comm 2]
        exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (by decide : 2 < 4800) sourceQ_large)
          (pow_pos sourceQ_pos _)
      _ = sourceQ^(100+1) := (pow_succ _ _).symm

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.instDecidablePredNatAndPrimeDvdHPowQcardOfNatHAdd
lemma prime_217 : prime 217=FiniteGeometry.sourcePrime := by
  apply le_antisymm
  · exact prime_le 217 _ FiniteGeometry.sourcePrime_prime FiniteGeometry.sourceD_divisible
  · exact FiniteGeometry.sourcePrime_le _ (prime_prime 217) (prime_congruent 217)
lemma degree_217 : degree 217=FiniteGeometry.sourceD := by
  simp only [degree,prime_217,FiniteGeometry.sourceD]
lemma dimension_217 : dimension 217=1200 := by
  unfold dimension blockdim exponent
  rw [degree_217]
  change 10*(Nat.log FiniteGeometry.sourceQ FiniteGeometry.sourceD+20)=1200
  rw [FiniteGeometry.sourceD_log]

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.LexicographicOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

lemma first_spec {α : Type u_2} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) :
    P (first P h) := by
  have hh := Finset.min'_mem (Finset.univ.filter P) (by simpa [Finset.Nonempty] using h)
  exact (Finset.mem_filter.mp hh).2

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.QuotientField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.two_neZero
attribute [local instance] OAI.KaplanskyCounterexample.Prescription.polynomialResidueOrder
attribute [local instance] OAI.KaplanskyCounterexample.Prescription.polynomialVectorOrder
def firstCoeffs (d : ℕ) (hd : 0 < d) : Fin (d+1) → ZMod 2 :=
  first (irreducibleCoeffs d) (irreducibleCoeffs_exists d hd)

def firstPolynomial (d : ℕ) (hd : 0 < d) : (ZMod 2)[X] := ofFn (d+1) (firstCoeffs d hd)

lemma firstPolynomial_monic (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).Monic :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).1
lemma firstPolynomial_degree (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).natDegree=d :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.1
lemma firstPolynomial_irreducible (d : ℕ) (hd : 0 < d) : Irreducible (firstPolynomial d hd) :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.2

/-- Exactly F₂[Z]/(g), with g the lexicographically first monic irreducible
polynomial of the prescribed degree. -/
abbrev CoefficientField (d : ℕ) (hd : 0 < d) := AdjoinRoot (firstPolynomial d hd)

instance firstPolynomial_fact (d : ℕ) (hd : 0 < d) : Fact (Irreducible (firstPolynomial d hd)) :=
  ⟨firstPolynomial_irreducible d hd⟩

instance coefficientField_finite (d : ℕ) (hd : 0 < d) : Finite (CoefficientField d hd) := by
  let : Module.Finite (ZMod 2) (CoefficientField d hd) :=
    (AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finite
  exact Module.finite_of_finite (ZMod 2)

instance coefficientField_fintype (d : ℕ) (hd : 0 < d) : Fintype (CoefficientField d hd) :=
  Fintype.ofFinite _

lemma coefficientField_finrank (d : ℕ) (hd : 0 < d) :
    finrank (ZMod 2) (CoefficientField d hd)=d := by
  rw [(AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim,firstPolynomial_degree]

lemma coefficientField_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CoefficientField d hd)=2^d := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,coefficientField_finrank]

@[instance_reducible] def coefficientFieldOrder (d : ℕ) (hd : 0 < d) :
    LinearOrder (CoefficientField d hd) :=
  letI : LinearOrder (Fin (firstPolynomial d hd).natDegree → ZMod 2) := vectorOrder
  LinearOrder.lift' (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun
    (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun.injective

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

def fieldDegree (h : Input) : ℕ := h.val*(prime h.val-1)
lemma fieldDegree_pos (h : Input) : 0 < fieldDegree h := by
  have := prime_ge h.val h.property
  exact Nat.mul_pos (by omega) (by omega)

abbrev K (h : Input) := CoefficientField (fieldDegree h) (fieldDegree_pos h)
instance K_field (input : Input) : Field (K input) := inferInstance

instance K_char (h : Input) : CharP (K h) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (K h)).injective 2

abbrev Q (h : Input) := rootSubfield (K h) h.val

instance K_order (h : Input) : LinearOrder (K h) := coefficientFieldOrder _ _

lemma K_card (h : Input) : Fintype.card (K h)=2^(fieldDegree h) :=
  coefficientField_card _ _
lemma Q_card (h : Input) : Fintype.card (Q h)=Qcard h.val := by
  apply rootSubfield_card (K h) h.val (by omega)
  rw [coefficientField_finrank]
  exact dvd_mul_right _ _

/-- The enumeration of the prescribed root subfield is in inherited coefficient order. -/
def enumeration (h : Input) : Fin (Qcard h.val) ≃ Q h :=
  (Fintype.orderIsoFinOfCardEq (Q h) (Q_card h)).toEquiv

lemma primitive_exists (h : Input) : ∃ ζ : K h, IsPrimitiveRoot ζ (prime h.val) := by
  let : Fact (prime h.val).Prime := ⟨prime_prime h.val⟩
  have hc : (2:ℕ).Coprime (prime h.val) := Nat.coprime_two_left.mpr (prime_odd h.val h.property)
  have hf := (Nat.ModEq.pow_card_sub_one_eq_one (prime_prime h.val) hc).pow h.val
  have hd : prime h.val ∣ Fintype.card (K h)ˣ := by
    rw [Fintype.card_units,K_card]
    simpa only [fieldDegree,← pow_mul,one_pow,Nat.mul_comm] using hf.symm.dvd'
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := (K h)ˣ) (prime h.val) hd
  refine ⟨u,IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  simpa only [orderOf_units] using hu

/-- The first element of multiplicative order ell in the literal coefficient order. -/
def zeta (h : Input) : K h := first (fun ζ => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)
lemma zeta_primitive (h : Input) : IsPrimitiveRoot (zeta h) (prime h.val) := by
  unfold zeta
  exact first_spec (fun ζ : K h => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.ParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma sourceD_square_le : sourceD^2 ≤ sourceQ^1200 :=
  small_degree_square (sourceQ_large.trans' (by decide)) sourceD_bounds.2

lemma source_frame_size : sourceD/sourceQ+(sourceD/sourceQ)*sourceQ ≤ sourceQ^120 :=
  small_degree_frame_size (sourceQ_large.trans' (by decide)) sourceD_bounds.2 sourceD_q_dvd

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.SimplexBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing
variable {Q : Type u_1} [Field Q] [Fintype Q] {q n d t : ℕ}

omit [Field Q] [Fintype Q] in
lemma simplex_density_bound (a : Fin q ≃ Q) (hn : 0 < n) (hq : 2*n ≤ q) :
    q^n ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := by
  obtain ⟨hcut,hfloor⟩ := small_cube_cutoff hn hq
  have hc := cube_card_le_simplex a (Nat.div_le_self q (2*n)) hcut
  calc
    q^n ≤ (4*n*(q/(2*n)))^n := Nat.pow_le_pow_left hfloor n
    _ = (4*n)^n * (q/(2*n))^n := mul_pow _ _ _
    _ ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := Nat.mul_le_mul_left _ hc

end KaplanskyCounterexample.PolynomialPairing
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open FiniteGeometry PolynomialPairing

structure Successful {Q : Type} [Field Q] [Fintype Q] {q n : ℕ}
    (a : Fin q ≃ Q) (ℓ : ℕ)
    (pair : Finset (Fin n → Q) × Finset (Finset (Fin n → Q))) : Prop where
  holes_subset : pair.1 ⊆ simplexPoints a n ((q-2)/2)
  lower : 2*q^n ≤ pair.1.card*(ℓ+1)^2
  upper : pair.1.card*(ℓ+1)^2 ≤ 7*q^n
  full : ∀ L ∈ pair.2, FullLine (Q := Q) L
  avoid : ∀ L ∈ pair.2, ∀ v ∈ L, v ∉ pair.1
  regular : ∀ v : {v : Fin n → Q // v ∉ pair.1},
    Fintype.card {L : pair.2 // v.val ∈ L.val}=ℓ+1
  girth : 12 ≤ (Planar.incidenceGraph
    (fun (v : {v : Fin n → Q // v ∉ pair.1}) (L : pair.2) => v.val ∈ L.val)).egirth

namespace DirectionFrame
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
  (F : FiniteGeometry.DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

lemma tradeLine_injective
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O) :
    Function.Injective (F.tradeLine O P T) := by
  intro i j hij
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    ((F.tradeLine_full O P T i).card ▸ Fintype.one_lt_card (α := Q))
  have hxj : x ∈ F.tradeLine O P T j := hij ▸ hx
  have hyj : y ∈ F.tradeLine O P T j := hij ▸ hy
  have hl : F.tradeLabel O P T i=F.tradeLabel O P T j := by
    by_contra hne
    have hz := Submodule.disjoint_def.mp (F.label_spaces_disjoint hne) (y-x)
      (F.tradeLine_step_mem O P T i hx hy) (F.tradeLine_step_mem O P T j hxj hyj)
    exact hxy (sub_eq_zero.mp hz).symm
  exact F.same_label_eq S O P T hO hl hx hxj

end DirectionFrame

/-- A faithful set of full lines from the successful geometric trade; the
bijection retains degrees and ordinary incidence girth exactly. -/
lemma successful_of_indexed {Q : Type} [Field Q] [Fintype Q] {q n ℓ : ℕ}
    (a : Fin q ≃ Q) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2))
    (hlow : 2*q^n ≤ O.card*(ℓ+1)^2) (hhigh : O.card*(ℓ+1)^2 ≤ 7*q^n)
    {I : Type} [Fintype I] (L : I → Finset (Fin n → Q)) (hinj : Function.Injective L)
    (hfull : ∀ i, FullLine (Q := Q) (L i))
    (havoid : ∀ i v, v ∈ L i → v ∉ O)
    (hdeg : ∀ v : {v : Fin n → Q // v ∉ O}, Fintype.card {i : I // v.val ∈ L i}=ℓ+1)
    (hgirth : 12 ≤ (Planar.incidenceGraph
      (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)).egirth) :
    ∃ pair, Successful (n := n) a ℓ pair := by
  let lines := Finset.univ.image L
  let f (i : I) : lines := ⟨L i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact hinj (congrArg Subtype.val h)
    · intro l
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp l.property
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective f hf
  refine ⟨(O,lines),⟨hO,hlow,hhigh,?_,?_,?_,?_⟩⟩
  · intro l hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact hfull i
  · intro l hl v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact havoid i v hv
  · intro v
    have ec := e.subtypeEquiv (p := fun i => v.val ∈ L i)
      (q := fun l => v.val ∈ l.val) (fun _ => Iff.rfl)
    exact (Fintype.card_congr ec).symm.trans (hdeg v)
  · let g : (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)) ≃g
        (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (l : lines) => v.val ∈ l.val)) :=
      { toEquiv := Equiv.sumCongr (Equiv.refl _) e
        map_rel_iff' := by intro v w; cases v <;> cases w <;> rfl }
    exact g.egirth_eq ▸ hgirth

/-- Uniformity in every enumeration and realization of F_(2^217), required
by the literal outer search (whose field is the lexicographic quotient). -/
lemma succeeds_217 (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (hq : Fintype.card Q=sourceQ) (a : Fin sourceQ ≃ Q) :
    ∃ pair : Finset (Fin 1200 → Q) × Finset (Finset (Fin 1200 → Q)),
      Successful a sourcePrime pair := by
  let R := Fin (sourceD/sourceQ)
  let E := Fin 119 → Q
  have hRcard : Fintype.card R=sourceD/sourceQ := Fintype.card_fin _
  have hr : Fintype.card R*sourceQ=sourceD := by
    rw [hRcard]
    exact Nat.div_mul_cancel sourceD_q_dvd
  obtain ⟨F⟩ := exists_coordinate_frame Q R (by
    simpa only [R,Fintype.card_fin,hq] using source_frame_size)
  let S := simplexPoints a 1200 ((sourceQ-2)/2)
  have hn : Fintype.card (Fin 1200 → Q)=sourceQ^1200 := by
    simp only [Fintype.card_fun,Fintype.card_fin,hq]
  have hE : Fintype.card E=sourceQ^119 := by
    simp only [E,Fintype.card_fun,Fintype.card_fin,hq]
  have hdensity : Fintype.card (Fin 1200 → Q) ≤ sourceQ^72*S.card := by
    rw [hn]
    have hs := simplex_density_bound (n := 1200) a (by decide) (by have := sourceQ_large; omega)
    rw [show 4*1200=4800 from rfl] at hs
    exact hs.trans (Nat.mul_le_mul_right S.card sourceQ_density)
  obtain ⟨O,hO,hlo,hhi⟩ := F.exists_sized_goodHoles S hq hE
    (sourceQ_large.trans' (by decide)) sourceD_bounds.1 (le_of_eq hr)
    hdensity (by rw [hn]; exact sourceD_square_le)
  have hRbound : Fintype.card R ≤ 2*(Fintype.card Q)^100 := by
    rw [hq,hRcard]
    exact (Nat.div_le_self sourceD sourceQ).trans sourceD_bounds.2
  obtain ⟨P,hP⟩ := F.exists_successfulSlabs_large S O hO (by rw [hq]; exact sourceQ_very_large)
    hRbound (by simp only [Module.finrank_pi,Fintype.card_fin])
  obtain ⟨T⟩ := F.exists_preliminary O P hP
  refine successful_of_indexed a O hO.source ?_ ?_ (F.tradeLine O P T)
    (DirectionFrame.tradeLine_injective F S O P T hO) (F.tradeLine_full O P T)
    (fun i v hv ho => Finset.disjoint_left.mp (F.tradeLine_avoid S O P T hO i) hv ho)
    ?_ (F.trade_incidence_girth S O P T hO hP)
  · simpa only [hn,sourceD] using hlo
  · have hb := hhi.trans (Nat.mul_le_mul_right (Fintype.card (Fin 1200 → Q)) (by decide : 3 ≤ 7))
    simpa only [hn,sourceD] using hb
  · intro v
    have hd := F.trade_degree S O P T hO v.val v.property
    rw [hq,hr] at hd
    simpa only [Fintype.card_eq_nat_card,sourceD] using hd

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Affine (h : Input) := Fin (dimension h.val) → Q h
abbrev Pair (h : Input) := Finset (Affine h) × Finset (Finset (Affine h))

/-- Coordinate-lex order, then indicator order for points and lines,
then indicator order for families, finally lexicographic order of the pair.
Discarding the non-full-line candidates does not change relative order. -/
@[instance_reducible] def pairOrder (h : Input) : LinearOrder (Pair h) :=
  letI : LinearOrder (Affine h) := vectorOrder
  letI : LinearOrder (Finset (Affine h)) := subsetOrder _
  letI : LinearOrder (Finset (Finset (Affine h))) := subsetOrder _
  LinearOrder.lift' (toLex : Pair h → Lex (Pair h)) (fun _ _ he => he)

def Test (h : Input) (p : Pair h) : Prop :=
  Successful (enumeration h) (prime h.val) p

def Succeeds (h : ℕ) : Prop := ∃ hh : 2 ≤ h, ∃ p, Test ⟨h,hh⟩ p

lemma succeeds217 : Succeeds 217 := by
  refine ⟨by decide,?_⟩
  let h : Input := ⟨217,by decide⟩
  have hs := succeeds_217 (Q h) (Q_card h) (enumeration h)
  have hn : dimension h.val=1200 := dimension_217
  have hp : prime h.val=FiniteGeometry.sourcePrime := prime_217
  unfold Test
  change ∃ p : Finset (Fin (dimension h.val) → Q h) ×
    Finset (Finset (Fin (dimension h.val) → Q h)), Successful (enumeration h) (prime h.val) p
  rw [hn,hp]
  exact hs

local instance instDecidablePredNatSucceeds : DecidablePred Succeeds := Classical.decPred _

/-- The exact least successful outer input, not the convenient existence bound 217. -/
def selectedH : ℕ := Nat.find (show ∃ h, Succeeds h from ⟨217,succeeds217⟩)
lemma selectedH_spec : Succeeds selectedH := Nat.find_spec _
lemma selectedH_ge : 2 ≤ selectedH := selectedH_spec.choose

def selectedInput : Input := ⟨selectedH,selectedH_ge⟩
lemma selectedInput_success : ∃ p, Test selectedInput p := selectedH_spec.choose_spec

/-- The first successful pair in the literal finite lexicographic search. -/
def selectedPair : Pair selectedInput :=
  letI := pairOrder selectedInput
  first (Test selectedInput) selectedInput_success

lemma selectedPair_spec : Test selectedInput selectedPair := by
  let _ := pairOrder selectedInput
  exact first_spec (Test selectedInput) selectedInput_success

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open IncidenceDirections
variable (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.directionModulusNeZero
/-- A direction is ordered by its full underlying point set. Slopes are just
coordinates for all of the one-dimensional subspaces, including the vertical one. -/
def directionSet (d : Option (ZMod ℓ)) : Finset (Fin 2 → ZMod ℓ) :=
  Finset.univ.image (directionMap d)

lemma directionSet_injective : Function.Injective (directionSet ℓ) := by
  intro d e he
  by_contra hne
  have hm : directionMap d 1 ∈ directionSet ℓ e := he ▸ Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hm
  have hh := directionMap_independent hne 1 (-c) (by simp [hc])
  exact one_ne_zero hh.1

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.directionResidueOrder
@[instance_reducible] def directionOrder : LinearOrder (Option (ZMod ℓ)) :=
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  letI : LinearOrder (Finset (Fin 2 → ZMod ℓ)) := subsetOrder _
  LinearOrder.lift' (directionSet ℓ) (directionSet_injective ℓ)

def orderedAssignment {V F : Type} [Fintype F] [LinearOrder F] (Inc : F → Finset V)
    (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f}=ℓ+1)
    (v : V) : {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ) :=
  letI := directionOrder ℓ
  ((Fintype.orderIsoFinOfCardEq {f : F // v ∈ Inc f} (hdeg v)).toEquiv.symm.trans
    (Fintype.orderIsoFinOfCardEq (Option (ZMod ℓ)) (by simp)).toEquiv)

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {V m : Type} [Fintype V] [Fintype m] [LinearOrder V] [LinearOrder m]

attribute [local instance] OAI.KaplanskyCounterexample.Prescription.slotModulusNeZero
attribute [local instance] OAI.KaplanskyCounterexample.Prescription.slotIndexWellFounded
def slotAssignment (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) :
    V ↪ m × (Fin 2 → ZMod ℓ) :=
  letI := slotPairOrder (m := m) ℓ
  let e := Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl
  let r := (Fintype.orderIsoFinOfCardEq V rfl).symm
  { toFun := fun v => e ⟨(r v).val, by
      have hc : Fintype.card (m × (Fin 2 → ZMod ℓ))=Fintype.card m * ℓ^2 := by simp
      rw [hc]
      exact (r v).isLt.trans_le hsize⟩
    inj' := by
      intro v w he
      apply r.injective
      apply Fin.ext
      have hh := e.injective he
      exact congrArg (fun z => z.val) hh }

def assignedSlot (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) : m :=
  (slotAssignment ℓ hsize v).1

def assignedForm (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) :
    CoordinateCharacters.Plane ℓ →* CoordinateCharacters.Cyclic ℓ :=
  CoordinateCharacters.form ℓ (slotAssignment ℓ hsize v).2

end KaplanskyCounterexample.Prescription
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.Prescription.Output
open PolynomialPairing

abbrev h := selectedInput
abbrev q := Qcard h.val
abbrev ell := prime h.val
abbrev n := dimension h.val
abbrev Coeff := K h
abbrev Subfield := Q h
abbrev Ambient := Affine h
abbrev holes : Finset Ambient := selectedPair.1
abbrev family : Finset (Finset Ambient) := selectedPair.2
abbrev V := {v : Ambient // v ∉ holes}
abbrev F := ↥family
abbrev Slots := ↥holes

instance ell_prime : Fact ell.Prime := ⟨prime_prime h.val⟩
local instance (priority := 3000) instDecidableEqSubtypeKHMemSubfieldSubfield : DecidableEq Subfield := Classical.decEq _
@[instance_reducible] instance ambient_order : LinearOrder Ambient := vectorOrder
@[instance_reducible] instance subsets_order : LinearOrder (Finset Ambient) := subsetOrder _
instance (priority := 2000) ambient_le : LE Ambient := ambient_order.toLE
instance (priority := 2000) ambient_lt : LT Ambient := ambient_order.toLT
instance (priority := 2000) subsets_le : LE (Finset Ambient) := subsets_order.toLE
instance (priority := 2000) subsets_lt : LT (Finset Ambient) := subsets_order.toLT
local instance (priority := 3000) instDecidableEqV : DecidableEq V := Classical.decEq _

lemma success : Successful (enumeration h) ell selectedPair := selectedPair_spec

def Inc (f : F) : Finset V := f.val.subtype (fun v => v ∉ holes)
lemma mem_Inc (v : V) (f : F) : v ∈ Inc f ↔ v.val ∈ f.val := Finset.mem_subtype

lemma nonempty_Inc (f : F) : (Inc f).Nonempty := by
  obtain ⟨v,hv⟩ := (success.full f.val f.property).nonempty
  exact ⟨⟨v,success.avoid f.val f.property v hv⟩,(mem_Inc _ _).mpr hv⟩
lemma degree_Inc (v : V) : Fintype.card {f : F // v ∈ Inc f}=ell+1 := by
  rw [Fintype.card_eq_nat_card]
  have hr := success.regular v
  rw [Fintype.card_eq_nat_card] at hr
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun f => mem_Inc v f))).trans hr
lemma girth_Inc : 12 ≤ (Planar.incidenceGraph (fun (v : V) (f : F) => v ∈ Inc f)).egirth := by
  have he : (fun (v : V) (f : F) => v ∈ Inc f) = (fun (v : V) (f : F) => v.val ∈ f.val) := by
    funext v f
    exact propext (mem_Inc v f)
  rw [he]
  exact success.girth

lemma ambient_card : Fintype.card Ambient=q^n := by
  change Fintype.card (Fin n → Q h)=q^n
  rw [Fintype.card_fun,Fintype.card_fin,Q_card]
lemma V_card : Fintype.card V=q^n-holes.card := by
  simp only [V,Fintype.card_subtype_compl,Fintype.card_coe,ambient_card]
lemma sizes : 0 < Fintype.card Slots ∧ Fintype.card Slots < Fintype.card V ∧
    Fintype.card V ≤ Fintype.card Slots*ell^2 := by
  rw [V_card,Fintype.card_coe]
  exact hole_size_inequalities (by rw [← ambient_card]; exact Fintype.card_pos)
    ((Finset.card_le_univ holes).trans_eq ambient_card) (prime_ge h.val h.property)
    success.lower success.upper

/-- The specified first point and first matrix coordinate in their inherited orders. -/
def v0 : V := first (fun _ => True) (by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (sizes.1.trans sizes.2.1)
  exact ⟨v,trivial⟩)
def i0 : Slots := first (fun _ => True) (by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp sizes.1
  exact ⟨i,trivial⟩)

def assignment : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ell) :=
  orderedAssignment ell Inc degree_Inc

def slot : V → Slots := assignedSlot ell sizes.2.2
def form : V → GluedGroup.PointGroup ell →* Multiplicative (ZMod ell) :=
  assignedForm ell sizes.2.2

/-- The unique interpolation columns over the actual prescribed root subfield. -/
def X : Matrix Slots V Coeff := complementMatrix (enumeration h) holes

end KaplanskyCounterexample.Prescription.Output
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.PrescribedOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription.Output
local instance (priority := 3000) instDecidableEqSubtypeKHMemSubfieldSubfield_1 : DecidableEq Subfield := Classical.decEq _

local instance (priority := 3000) instDecidableEqV_1_r4056fb_1 : DecidableEq V := Classical.decEq _
/-- The group in the literal prescription: the coordinate gluing, its multiple
HNN extension and the finite permutation/character block. -/
abbrev G := ChosenCriterion.Group (m := Slots) ell Inc assignment nonempty_Inc girth_Inc v0 form

def a : MonoidAlgebra Coeff G :=
  ChosenCriterion.aOut ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot

def b : MonoidAlgebra Coeff G :=
  ChosenCriterion.bOut ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot

def N_shortEquiv :
    PresentedGroup (GluedGroup.shortRelators Inc ell
      (AssignedDirections.incidenceMap Inc ell assignment)) ≃*
    AssignedDevelopment.Base Inc ell assignment :=
  GluedGroup.shortEquiv Inc ell _ (AssignedDevelopment.covers Inc ell assignment)

end KaplanskyCounterexample.Prescription.Output
end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.OddTorsion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded cyclic subgroup of odd prime order in the prescribed group. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.Prescription.Output

def diagonalPoint : Multiplicative (ZMod ell) →* GluedGroup.PointGroup ell where
  toFun c := Multiplicative.ofAdd (fun _ => c.toAdd)
  map_one' := rfl
  map_mul' _ _ := rfl

def retainedPoint : GluedGroup.PointGroup ell →* G :=
  (MonoidHom.inl _ _).comp
    ((CharacterTwist.emb (ChosenCriterion.inclusion ell Inc assignment)
      (ChosenCriterion.inclusion_injective ell Inc assignment nonempty_Inc girth_Inc)
      v0 form).comp
        ((MonoidHom.inl _ _).comp (AssignedDevelopment.point Inc ell assignment v0)))

end KaplanskyCounterexample.Prescription.Output

end

end OAI
end


