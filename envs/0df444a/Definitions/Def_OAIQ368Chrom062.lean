-- Prove2me | Definitions.Def_OAIQ368Chrom062
-- name    : OAIQ368Chrom062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:01:47.781823+00:00
-- url     : https://prove2.me/theorems/16fe95fc-3c70-4f11-a659-33fb1d432503
-- title:
--   Definitions bundle OAIQ368Chrom062 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 11 definitions, 11 instances and 13 theorems. The definitions and types are `OAI.ElementaryPositivity.CoefficientReflection.reflect`, `OAI.ElementaryPositivity.CoefficientReflection.reflectPolynomial`, `OAI.ElementaryPositivity.ElementaryRigidity.eval`, `OAI.ElementaryPositivity.ElementaryRigidity.partitionPolynomial`, `OAI.ElementaryPositivity.FiniteSearch.Row`, `OAI.ElementaryPositivity.FiniteSearch.Table`, `OAI.ElementaryPositivity.FiniteSearch.matrixCount`, `OAI.ElementaryPositivity.FiniteSearch.rowPartition`, `OAI.ElementaryPositivity.FiniteSearch.rowProfile`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean), [`Chromatic_Witness_ElementaryAlphabetRigidity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementaryAlphabetRigidity.lean), [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom063`, `OAIQ368Chrom064` and `OAIQ368Chrom068`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ368_CHROM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed non-unital ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b's `Subtype.starOrderedRing` is an
instance for every closed non-unital ⋆-subalgebra class; OpenAI's projection corners rely on it, q360). -/
instance nonUnitalStarSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ}

lemma rev_adjacent {i j : Fin n} (h : i.val + 1 = j.val) :
    j.rev.val + 1 = i.rev.val := by
  simp only [Fin.rev]
  omega

end ElementaryPositivity.NaturalUnitIntervalGraph

namespace ElementaryPositivity.CoefficientReflection

noncomputable def reflectPolynomial (M : ℕ) : Polynomial ℕ →+ Polynomial ℕ where
  toFun := Polynomial.reflect M
  map_zero' := Polynomial.reflect_zero
  map_add' p q := Polynomial.reflect_add p q M

noncomputable def reflect {α : Type*} (M : ℕ) :
    MvPolynomial α (Polynomial ℕ) →+ MvPolynomial α (Polynomial ℕ) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom (reflectPolynomial M)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

lemma map_esymmPart {α : Type*} [Fintype α] {n : ℕ} (lam : Nat.Partition n) :
    MvPolynomial.map (Polynomial.C : ℕ →+* Polynomial ℕ)
      (MvPolynomial.esymmPart α ℕ lam) = MvPolynomial.esymmPart α (Polynomial ℕ) lam := by
  simp only [MvPolynomial.esymmPart, map_multiset_prod, Multiset.map_map,
    Function.comp_def, MvPolynomial.map_esymm]

end ElementaryPositivity.CoefficientReflection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_HistoryMainWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators

abbrev Row (n:ℕ):={v:Fin n → Fin (n+1) // ∑i,(v i).val=n}

def rowPartition {n:ℕ} (v:Row n):Nat.Partition n:=
  Nat.Partition.ofSums n (Finset.univ.val.map (fun i=>(v.val i).val)) v.property

lemma rowPartition_surjective (n:ℕ) : Function.Surjective (@rowPartition n) := by
  intro p
  obtain ⟨l,hl⟩:=Quotient.exists_rep p.parts
  have hl':(l:Multiset ℕ)=p.parts:=hl
  have hsum:l.sum=n:=by simpa only [←hl',Multiset.sum_coe] using p.parts_sum
  have hpos:∀i∈l,0 < i:=by intro i hi; exact p.parts_pos (by simpa only [←hl',Multiset.mem_coe] using hi)
  have hlen:l.length≤n:=hsum ▸ List.length_le_sum_of_one_le l hpos
  let L:=l++List.replicate (n-l.length) 0
  have hL:L.length=n:=by simp [L]; omega
  have hbL:∀x∈L,x≤n:=by
    intro x hx
    simp only [L,List.mem_append,List.mem_replicate] at hx
    rcases hx with hx|⟨_,hx⟩
    · exact p.le_of_mem_parts (by simpa only [←hl',Multiset.mem_coe] using hx)
    · omega
  let v:Fin n → Fin (n+1):=fun i=>⟨L[i.val]'(by omega),
    Nat.lt_succ_of_le (hbL _ (List.getElem_mem (by omega)))⟩
  have hv:List.ofFn (fun i:Fin n=>(v i).val)=L:=by
    apply List.ext_getElem
    · simp [hL]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hm:(Finset.univ.val.map (fun i:Fin n=>(v i).val):Multiset ℕ)=L:=by
    rw [Finset.val_univ_fin]
    change (List.map (fun i:Fin n=>(v i).val) (List.finRange n):Multiset ℕ)=_
    rw [←List.ofFn_eq_map,hv]
  have hvsum:(∑i:Fin n,(v i).val)=n:=by
    change (Finset.univ.val.map (fun i:Fin n=>(v i).val)).sum=n
    rw [hm,Multiset.sum_coe]
    simp [L,hsum]
  refine ⟨⟨v,hvsum⟩,?_⟩
  apply Nat.Partition.ext
  change (Finset.univ.val.map (fun i:Fin n=>(v i).val)).filter (·≠0)=p.parts
  rw [hm,←hl']
  have hf:(l:Multiset ℕ).filter (·≠0)=(l:Multiset ℕ):=
    Multiset.filter_eq_self.mpr (by intro i hi; exact (hpos i hi).ne')
  simpa [L] using hf

end ElementaryPositivity.FiniteSearch

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
variable {n:ℕ}

abbrev Table (n:ℕ):=(Fin n → Fin n) → Row n

def matrixCount (v:Row n) (a:Fin n → ℕ):ℕ:=∑s:Fin n → Finset (Fin n),
  if (∀i,(s i).card=(v.val i).val) ∧
    (∀c,(Finset.univ.filter (fun i=>c∈s i)).card=a c) then 1 else 0

end ElementaryPositivity.FiniteSearch

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

def rowProfile (v:Row n):Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun i=>(v.val i).val)
lemma rowProfile_degree (v:Row n):(rowProfile v).degree=n:=by
  rw [Finsupp.degree_eq_sum]
  exact v.property
end
end ElementaryPositivity.FiniteSearch

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementaryAlphabetRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ElementaryRigidity
open scoped BigOperators
open Classical
noncomputable section
variable {n r:ℕ} {R S:Type*} [CommSemiring R] [CommSemiring S]

def eval (n r:ℕ) (R:Type*) [CommSemiring R] :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin r) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>MvPolynomial.esymm (Fin r) R (i.val+1))

def partitionPolynomial (lam:Nat.Partition n) : MvPolynomial (Fin n) R :=
  (lam.parts.attach.map (fun k=>MvPolynomial.X (⟨k.val-1,by
    have hp:=lam.parts_pos k.property
    have hb:=lam.le_of_mem_parts k.property
    omega⟩:Fin n))).prod

lemma eval_partition (lam:Nat.Partition n) (r:ℕ) :
    eval n r R (partitionPolynomial (R:=R) lam)=MvPolynomial.esymmPart (Fin r) R lam := by
  unfold partitionPolynomial MvPolynomial.esymmPart
  rw [map_multiset_prod,Multiset.map_map]
  have he:∀k:{k // k∈lam.parts},
      eval n r R (MvPolynomial.X (⟨k.val-1,by
        have hp:=lam.parts_pos k.property
        have hb:=lam.le_of_mem_parts k.property
        omega⟩:Fin n))=MvPolynomial.esymm (Fin r) R k.val:=by
    intro k
    simp only [eval,MvPolynomial.eval₂Hom_X']
    rw [Nat.sub_add_cancel (lam.parts_pos k.property)]
  simp_rw [Function.comp_def,he]
  have H:=congrArg (fun l:Multiset ℕ=>(l.map (MvPolynomial.esymm (Fin r) R)).prod)
    (Multiset.attach_map_val lam.parts)
  simpa only [Multiset.map_map,Function.comp_def] using H

lemma map_eval (f:R →+* S) (p:MvPolynomial (Fin n) R) :
    MvPolynomial.map f (eval n r R p)=eval n r S (MvPolynomial.map f p) := by
  unfold eval
  rw [MvPolynomial.map_eval₂Hom,MvPolynomial.eval₂Hom_map_hom]
  simp only [MvPolynomial.map_esymm]
  congr 2
  ext x
  simp

lemma eval_injective_ring (R:Type*) [CommRing R] (n:ℕ) : Function.Injective (eval n n R) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective R le_rfl
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply,MvPolynomial.esymmAlgHom_apply]
  exact h

lemma eval_injective_natPolynomial (n:ℕ) : Function.Injective (eval n n (Polynomial ℕ)) := by
  let f:Polynomial ℕ →+* Polynomial ℤ:=Polynomial.mapRingHom (Nat.castRingHom ℤ)
  have hf:Function.Injective f:=Polynomial.map_injective (Nat.castRingHom ℤ) (by intro a b h; change (a:ℤ)=(b:ℤ) at h; exact Int.ofNat_inj.mp h)
  intro p q h
  apply MvPolynomial.map_injective f hf
  apply eval_injective_ring (Polynomial ℤ) n
  rw [←map_eval,←map_eval,h]

lemma eval_C (x:R) : eval n r R (MvPolynomial.C x)=MvPolynomial.C x :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma uniform_of_at_n {A:Type*} [Fintype A] (E:A → ℕ)
    (lam μ:A → Nat.Partition n)
    (h:(∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (μ a))
    (r:ℕ) :
    (∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (μ a) := by
  have he:(∑a,MvPolynomial.C (Polynomial.X^E a)*partitionPolynomial (R:=Polynomial ℕ) (lam a))=
      ∑a,MvPolynomial.C (Polynomial.X^E a)*partitionPolynomial (R:=Polynomial ℕ) (μ a):=by
    apply eval_injective_natPolynomial n
    simpa only [map_sum,map_mul,eval_partition,eval_C] using h
  have H:=congrArg (eval n r (Polynomial ℕ)) he
  simpa only [map_sum,map_mul,eval_partition,eval_C] using H
end
end ElementaryPositivity.ElementaryRigidity

end

end OAI
end


