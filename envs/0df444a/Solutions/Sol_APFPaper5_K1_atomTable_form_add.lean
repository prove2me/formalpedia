-- Prove2me | solution 1 for APFPaper5.K1.atomTable_form_add
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:02:26.425297+00:00
-- url     : https://prove2.me/submissions/45822aa2-821c-4136-adff-36b539fc523b

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-18; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K1_the_table_at_one_price
title: With every record at one price, each entry of the record-book table is epsilon times a count of records, and its form on combinations is epsilon times a sum of squares, one square for each record
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 5acc74a15148f2947f6a1f0195f878c448ac62a5f255305a5fafa7352b05bd8c), kept in Old/ as
 Thm_APFPaper5_K1_the_table_at_one_price_pre-restating_v57_2026-11-21.lean. No declaration is changed. THE
 RESTATED BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, which was 2026-11-17.4, and this
 entry. Nothing else.
 WHAT HAPPENED: since revision 2026-11-17.4, which this header named until now, three revisions of
 FOUNDATION_INPUTS were installed. Revision 2026-11-18.2, installed 2026-11-18 at 18:22 HST (sha256
 290a59cad5591706d9b929fc98dde9f1b1215b4e40dc3d8eff790e8c59090cf0;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-18.2_2026-11-18): the reading of B02's first sentence
 (reading_20261114_list_complete) is scoped to what is recorded. It now reads: "The distinctions of a
 context are complete for what is recorded: potential states that every distinction of the context reads
 alike are recorded alike. They may differ in what they hold unrecorded. Then what can follow them tells
 them apart, and no side does." It is a reading and not a commitment; B02's two sentences are unchanged.
 Revision 2026-11-18.3, installed 2026-11-18 at 19:50 HST (sha256
 95815d3a9ef01dd631bd52729a66a79531ff4590ed44d451be5882af20cc35b2;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-18.3_and_GATE_POLICY_2026-11-18.inputs.2_2026-11-18): one block
 was added that records where 13 cited files now resolve. No wording of a commitment changed. Revision
 2026-11-20.2, installed 2026-11-20 at 12:36 HST (sha256
 05c831bf6e786f168d9a9f0bb366b496388bd049960e9df3ca0acad8680d6252;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-20.2_2026-11-20): B06 is reduced. After its first four sentences,
 which are unchanged, it now reads: "To draw a distinction is to keep its record: each distinction has one
 record, the same in every protocol, and a protocol draws the distinction exactly when it keeps that record.
 Every record a protocol keeps is the record of some tested distinction or family of tested distinctions,
 and is used for it. Every process pays epsilon for each record it keeps, and nothing else, where epsilon is
 positive and fixed by the context. In every context some protocol draws no distinction. The occupant draws
 exactly its family, and every part of that family is drawn alone by some protocol. A process that keeps no
 record costs nothing. A process that keeps no record changes nothing that is recorded." Against revision
 2026-11-18.3, six sentences are replaced by four and three are kept word for word. The six that are no
 longer sentences of the inputs: "Each record carries a cost. What a set of records is sufficient for does
 not depend on the protocol that keeps it. The occupant holds its distinctions with exactly the records they
 need, and its bill is the cost of those records. The same is true of every part of it: any family of its
 distinctions is held with exactly the records that family needs, at exactly their cost, and there is no
 cheaper way to hold that family. Epsilon is the unit of the occupant: each record it keeps costs epsilon,
 the floor of its context. Holding nothing costs nothing." B03 and B05 are retired as inputs and are kept in
 the inputs file as derived statements. B07a and B07b each gain a note, note_20261120_protocol_binding;
 their wording, scope and forms are unchanged. B01, B02 and B04 are unchanged. The commitments are six: B01,
 B02, B04, B06, B07a, B07b. The gate policy on the build machine is policy_revision 2026-11-20.inputs.1
 (sha256 5e9f3ec3cfa6c9a0a0b28549d13370c31ef78de38272ac6391efeac472f9a4aa) and requires this revision
 (INSTALL_RECEIPT_GATE_POLICY_2026-11-20.inputs.1_2026-11-20).
 HOW TO READ THE REST OF THIS HEADER: it named revision 2026-11-17.4 and is left as written, any earlier
 entries "restated" below included. Where it names revision 2026-11-17.4 or an earlier one as the revision
 in force, that is no longer so: the revision in force is 2026-11-20.2. Where it counts eight commitments,
 eight inputs or eight declared forms: there are now six commitments. The declared forms of B03 and B05 are
 unchanged and are now forms of derived statements. Where it calls B03 or B05 an input, or takes the
 declared form of either as a hypothesis: the installed file says of B03, and in the same words of B05, "A
 dependency on B03 is a dependency on its declared form, which is unchanged. From revision 2026-11-20.2 that
 form is a derived statement and not an input. The derivation is a draft and is not certified: until it is
 admitted through the gate, a node that consumes B03 is conditional on it. Resolve it before foundation
 certification. Do not treat an old use of B03 as a use of B06." Where it speaks of B06 by a count of its
 sentences or by their numbers, of the occupant statement, of the amended B06, or of a sentence of B06 as an
 input: that is B06 as it stood at the revision the header then named, and B06 now reads as quoted above. A
 statement here that takes one of the six replaced sentences as a premise stays true as a conditional;
 whether it follows from the reduced B06 is NOT SAID by this entry (for what used them see
 MEMO_pullbacks_passes119_and_120_what_used_the_dropped_sentences_and_one_world_for_all_eleven_2026-11-18 in
 Notes). Where it says of a sentence that is in B06 as quoted above that it is proposed, a ruling carried as
 a named hypothesis, NOT RULED, not installed or not an input: that is no longer so, for that sentence as
 worded above and for no typing of it. Where it takes the reading of B02's first sentence as first recorded
 (the distinctions of a context are complete: potential states that every distinction reads alike have the
 same continuation profile; the physical objects of a context correspond one to one with the combinations of
 sides of its distinctions) as a reading of the inputs: from revision 2026-11-18.2 the inputs do not assert
 it. A statement that takes it as a premise stays true as a conditional. A supplied world in which it holds
 is not excluded: the scoped reading adds no constraint. THE NEW SENTENCES OF B06 HAVE NO CERTIFIED LEAN
 FORM: the forms the inputs file names for the reduced B06 are drafts of the two seats, marked
 PROPOSED_NOT_CERTIFIED, and the Lean that derives the declared forms of B03 and B05 is a draft and is not
 gated. NOTHING in this entry says that a theorem of this file follows from the inputs at revision
 2026-11-20.2, or that a supplied world of this file is a world of them: each theorem stands as before, on
 its named hypotheses or on its supplied world, and a supplied world that breaks a sentence of the inputs at
 revision 2026-11-20.2 is not a world of the inputs at that revision, whatever this header says of an
 earlier one. The gate policy says of the move to this revision: "immutable; dependency compatibility must
 be established separately; no stale-basis waiver". This entry establishes no such compatibility. Proposed
 revision 2026-11-20.3 (one further note on each of B07a and B07b) is NOT installed.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-18 07:14 HST: "I'm worried about the loss of the sum of squares - don't we need
 that for quantum?", after this seat's note that under "every protocol pays epsilon for each record it
 keeps, and nothing else" (his ruling of 05:48 HST) a protocol's bill is a whole number of epsilons, while
 K3's supplied models price a held component by a sum of squares.
 Consulted before typing. Paper 5 Supplement v7.33: 250-292 (the closed-ledger polarization theorem: a
 faithful, two-homogeneous, parallelogram-complete cost q is B(x,x) for a unique positive-definite
 symmetric bilinear form); 294-298 ("Nonnegative cost and finiteness do not imply the parallelogram
 identity"); 384-391 ("The free real vector spaces on E and P carry the unique bilinear extension of s";
 "The parallelogram identity is therefore derived from bilinearity rather than added as an independent
 scalar-cost postulate"); 3037-3041 (K1: "one completed ordered score ... The bilinearization theorem is
 conditional on these physical data"). The builder seat's Def_APFPaper5_K1_MarkTable (tableForm,
 atomTable) and Thm_APFPaper5_K1_record_book_table (2026-11-12: atomTable_form, the form of the table on
 a combination is the weighted sum over records of the square of the combination's value on the record;
 atomTable_symm; record_book_table_satisfies_K1), Thm_APFPaper5_K1_mark_table_instance
 (tableForm_isBilinear). The builder seat's Thm_APFPaper5_K3_cost_invariant, which says it does not claim
 "that the price in A2 is the cost on combinations used in the plane theorem". Codebank:
 nonlocal_tie_resolution.py ("The framework's cost is COUNT-ONLY").
standing: ORDINARY MATHEMATICS on a record book: a finite type of records, Boolean marks on it, and one
 price for every record. No declared input is used as a hypothesis and none is proved.
what this file says:
 1. atomTable_at_one_price. With every record at epsilon, the table's entry for two marks is epsilon times
    the number of records both are listed against. Each entry is a whole number of epsilons.
 2. atomTable_form_at_one_price. The form of that table on a combination with real coefficients is epsilon
    times a sum of squares, one for each record: the square of the combination's value on that record.
    This is the builder seat's atomTable_form at equal weights.
 3. atomTable_form_add. For any weights, the form on a recombination is the two forms plus twice the cross
    term.
reading: the sum of squares is the form of the table on combinations. It is there for any nonnegative
 prices of records, as a weighted sum of squares; one price makes the weights equal. What one price makes
 a whole number of epsilons is each entry of the table and each protocol's bill, not the value of the form
 on a combination with real coefficients.
not_claimed: that the value of the form on a combination is any protocol's bill; where real coefficients
 come from (K1's bilinearization is conditional on physical data, Paper 5 Supplement 3037-3041); that an
 interface is a record book; that K3's two-component models are this form at an interface (ledger row
 C12, not built); anything about probabilities. No lane. No claim that the transfer is forced, that the
 carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

omit [Fintype ι] in
/-- With every record at epsilon, the table's entry for two marks is epsilon times the number of records
both are listed against. -/
theorem atomTable_at_one_price_p2mProof (eps : ℝ) (mark : ι → W → Bool) (i j : ι) :
    atomTable (fun _ => eps) mark i j =
      eps * ((Finset.univ.filter (fun a => mark i a = true ∧ mark j a = true)).card : ℝ) := by
  show ∑ a, eps * (ind (mark i a) * ind (mark j a)) = _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases hi : mark i a <;> cases hj : mark j a <;> simp [ind]

/-- With every record at epsilon, the form of the table on a combination is epsilon times a sum of
squares, one for each record. -/
theorem atomTable_form_at_one_price_p2mProof (eps : ℝ) (mark : ι → W → Bool) (x : ι → ℝ) :
    tableForm (atomTable (fun _ => eps) mark) x x =
      eps * ∑ a, (∑ i, x i * ind (mark i a)) ^ 2 := by
  rw [atomTable_form, Finset.mul_sum]

/-- The form on a recombination is the two forms plus twice the cross term. -/
theorem atomTable_form_add_p2mProof (w : W → ℝ) (mark : ι → W → Bool) (x y : ι → ℝ) :
    tableForm (atomTable w mark) (x + y) (x + y) =
      tableForm (atomTable w mark) x x + tableForm (atomTable w mark) y y +
        2 * tableForm (atomTable w mark) x y := by
  obtain ⟨hadd1, _, hadd2, _⟩ := tableForm_isBilinear (atomTable w mark)
  rw [hadd1, hadd2, hadd2, tableForm_symm (atomTable w mark) (atomTable_symm w mark) y x]
  ring

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] {W : Type apfNative_v} [inst_1 : Fintype.{apfNative_v} W]
  (w : W → Real) (mark : ι → W → Bool) (x y : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_u} ι inst (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark)
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} (ι → Real) (ι → Real) (ι → Real)
        (@instHAdd.{apfNative_u} (ι → Real)
          (@Pi.instAdd.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAdd))
        x y)
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} (ι → Real) (ι → Real) (ι → Real)
        (@instHAdd.{apfNative_u} (ι → Real)
          (@Pi.instAdd.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAdd))
        x y))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) x x)
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) y y))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) x y))) := by
  exact @APFPaper5.K1.atomTable_form_add_p2mProof
