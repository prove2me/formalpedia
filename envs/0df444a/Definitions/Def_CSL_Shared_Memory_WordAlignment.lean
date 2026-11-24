-- Prove2me | Definitions.Def_CSL_Shared_Memory_WordAlignment
-- name    : CSL_Shared_Memory_WordAlignment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:56:23.283214+00:00
-- url     : https://prove2.me/theorems/e2f64a39-ffcb-41c1-88f1-c65275b110e3
-- title:
--   Coded sorting library: Shared / Memory / WordAlignment
-- statement:
--   Module `CodedSorting.Shared.Memory.WordAlignment` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Physical cyclic role partitioning. The implementation transposes complete
--   prefix segments with an actual buffered disk pass, then splits the contiguous
--   result into separately aligned files. Gathering executes the inverse passes.
--   No permutation or pack of payload lists is an executable instruction.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.WordAlignment

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_PhysicalRecursiveExchange
import Definitions.Def_CSL_Shared_Words_WordConvention

section PhysicalRolePartition
/-! Physical cyclic role partitioning. The implementation transposes complete
prefix segments with an actual buffered disk pass, then splits the contiguous
result into separately aligned files. Gathering executes the inverse passes.
No permutation or pack of payload lists is an executable instruction. -/
namespace CSL.PhysicalRolePartition
open BucketMachine BucketReader TagErasure DiskStreamPass PhysicalFilePartition
open TriangularStreams
variable {Value : Type*} {R K C : ℕ}

/-- Input order is row, role, internal offset. Output order is role, row,
internal offset. The cardinality cast alone preserves numeric addresses. -/
def sourceCode : TripleAddress R K C ≃ Fin (K*(R*C)) :=
  tripleEncode.trans (finCongr (by ring))

def swapCoordinates : TripleAddress R K C ≃ TripleAddress K R C where
  toFun x := (x.2.1,x.1,x.2.2)
  invFun x := (x.2.1,x.1,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rolePermutation : Equiv.Perm (Fin (K*(R*C))) :=
  sourceCode.symm.trans (swapCoordinates.trans tripleEncode)

def sourceKey (x : Fin (K*(R*C))) : Fin K := (sourceCode.symm x).2.1

def targetKey (x : Fin (K*(R*C))) : Fin K :=
  (tripleEncode.symm x : TripleAddress K R C).1

@[simp] theorem permutation_encoded (x : TripleAddress R K C) :
    rolePermutation (sourceCode x) = tripleEncode (x.2.1,x.1,x.2.2) := by
  simp [rolePermutation,swapCoordinates]

@[simp] theorem inverse_encoded (x : TripleAddress K R C) :
    rolePermutation.symm (tripleEncode x) = sourceCode (x.2.1,x.1,x.2.2) := by
  simp [rolePermutation,swapCoordinates]

theorem sourceCode_lt (x y : TripleAddress R K C) :
    sourceCode x < sourceCode y ↔ tripleEncode x < tripleEncode y := by
  rfl

/-- Every role is read and written in its original row/offset order. -/
theorem role_increasing (x y : Fin (K*(R*C))) (hxy : x < y)
    (hk : sourceKey x = sourceKey y) : rolePermutation x < rolePermutation y := by
  obtain ⟨x,rfl⟩ := sourceCode.surjective x
  obtain ⟨y,rfl⟩ := sourceCode.surjective y
  simp only [sourceKey,Equiv.symm_apply_apply] at hk
  rw [permutation_encoded,permutation_encoded,tripleEncode_lt_iff]
  right
  refine ⟨hk,?_⟩
  have h := (tripleEncode_lt_iff x y).mp ((sourceCode_lt x y).mp hxy)
  rcases h with h | ⟨hrow,hrole | ⟨_,hoff⟩⟩
  · exact Or.inl h
  · rw [hk] at hrole
    exact (lt_irrefl _ hrole).elim
  · exact Or.inr ⟨hrow,hoff⟩

theorem inverse_increasing (x y : Fin (K*(R*C))) (hxy : x < y)
    (hk : targetKey x = targetKey y) : rolePermutation.symm x < rolePermutation.symm y := by
  obtain ⟨x,rfl⟩ := tripleEncode.surjective x
  obtain ⟨y,rfl⟩ := tripleEncode.surjective y
  simp only [targetKey,Equiv.symm_apply_apply] at hk
  rw [inverse_encoded,inverse_encoded,sourceCode_lt,tripleEncode_lt_iff]
  have h := (tripleEncode_lt_iff x y).mp hxy
  rcases h with h | ⟨_,hrow | ⟨hrow,hoff⟩⟩
  · rw [hk] at h
    exact (lt_irrefl _ h).elim
  · exact Or.inl hrow
  · exact Or.inr ⟨hrow,Or.inr ⟨hk,hoff⟩⟩

/-- Semantic contents of the physical role files. This definition is not
used by the executable scatter or gather. -/
def roleValues (F : Fin (K*(R*C)) → Value) (r : Fin K) : List Value :=
  List.ofFn (fun i : Fin (R*C) => F (rolePermutation.symm (finProdFinEquiv (r,i))))

def rolePieces (F : Fin (K*(R*C)) → Value) : List (List Value) :=
  List.ofFn (roleValues F)

theorem output_grouped (F : Fin (K*(R*C)) → Value) :
    outputValues rolePermutation F = (rolePieces F).flatten := by
  unfold outputValues rolePieces roleValues
  rw [← List.ofFn_eq_map,List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext r
  apply congrArg List.ofFn
  funext i
  congr 2
  apply Fin.ext
  simp only [finProdFinEquiv_apply_val]
  ring

@[simp] theorem rolePieces_length (F : Fin (K*(R*C)) → Value) :
    (rolePieces F).length=K := by simp [rolePieces]

@[simp] theorem rolePieces_lengths (F : Fin (K*(R*C)) → Value) :
    (rolePieces F).map List.length=List.replicate K (R*C) := by
  simp [rolePieces,roleValues,List.map_ofFn,Function.comp_def,List.ofFn_const]

@[simp] theorem rolePieces_volume (F : Fin (K*(R*C)) → Value) :
    (rolePieces F).flatten.length=K*(R*C) := by
  rw [← output_grouped]
  simp [outputValues]

/-- Public sizes control both loops. Source payload is accessed only by
Reader.pop inside the pass and the subsequent sequential splitter. -/
def scatterRoles (R K C B : ℕ) (source : List (List Value)) :
    Option (List (List (List Value)) × ℕ) := do
  let pass ← DiskStreamPass.run (rolePermutation (R := R) (K := K) (C := C)) sourceKey B source
  let split ← scatter B (List.replicate K (R*C)) pass.output.finish
  return (split.1,pass.transfers+split.2)

def gatherRoles (R K C B : ℕ) (files : List (List (List Value))) :
    Option (List (List Value) × ℕ) := do
  let joined ← gather B (files.map (fun file => (⟨file,R*C⟩ : File Value)))
  let pass ← DiskStreamPass.run (rolePermutation (R := R) (K := K) (C := C)).symm targetKey B joined.1
  return (pass.output.finish,joined.2+pass.transfers)

/-- The bound includes the transpose's source and output scans, every bucket
flush/refill, and the additional canonical-file split including short files. -/
theorem scatterRoles_correct (F : Fin (K*(R*C)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost,
      scatterRoles R K C B (pack B hB (inputValues F)) =
        some ((rolePieces F).map (pack B hB),cost) ∧
      cost ≤ 4*((K*(R*C))/B)+2*K+2+scanCost B hB (rolePieces F) := by
  obtain ⟨pass,hp,hf,hcost,_,_⟩ :=
    run_packed_canonical rolePermutation sourceKey role_increasing F B hB
  have hs := scatter_canonical B hB (rolePieces F)
  rw [rolePieces_lengths] at hs
  refine ⟨pass.transfers+scanCost B hB (rolePieces F),?_,by omega⟩
  simp [scatterRoles,hp,hf,output_grouped,hs,scanCost]

/-- Gather reconstructs the exact canonical original disk, including block
boundaries; the inverse permutation is executed rather than merely asserted. -/
theorem gatherRoles_correct (F : Fin (K*(R*C)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost,
      gatherRoles R K C B ((rolePieces F).map (pack B hB)) =
        some (pack B hB (inputValues F),cost) ∧
      cost ≤ scanCost B hB (rolePieces F)+4*((K*(R*C))/B)+2*K+2 := by
  let target : Fin (K*(R*C)) → Value := fun x => F (rolePermutation.symm x)
  obtain ⟨pass,hp,hf,hcost,_,_⟩ :=
    run_packed_canonical rolePermutation.symm targetKey inverse_increasing target B hB
  have hin : inputValues target=(rolePieces F).flatten := output_grouped F
  have hout : outputValues rolePermutation.symm target=inputValues F := by
    simp [target,outputValues,inputValues]
  rw [hin] at hp
  rw [hout] at hf
  have hd : ((rolePieces F).map (pack B hB)).map (fun file => (⟨file,R*C⟩ : File Value)) =
      descriptors B hB (rolePieces F) := by
    simp only [List.map_map,descriptors]
    apply List.map_congr_left
    intro piece hm
    have he : piece.length=R*C := by
      have := List.mem_map_of_mem (f := List.length) hm
      rw [rolePieces_lengths] at this
      exact (List.mem_replicate.mp this).2
    simp [Function.comp_def,he]
  have hg := gather_canonical B hB (rolePieces F)
  refine ⟨scanCost B hB (rolePieces F)+pass.transfers,?_,by omega⟩
  simp [gatherRoles,hd,hg,hp,hf,scanCost,Nat.add_comm]

/-- One combined coefficient for every input size, including empty and
sub-block files. K is the fixed role count, independent of recursion depth. -/
theorem partition_cost_bound (F : Fin (K*(R*C)) → Value) (B : ℕ) (hB : 0 < B) :
    (4*((K*(R*C))/B)+2*K+2+scanCost B hB (rolePieces F))*B ≤
      6*(K*(R*C))+(3*K+3)*B := by
  have hs := scanCost_bound B hB (rolePieces F)
  rw [rolePieces_volume,rolePieces_length] at hs
  have hd := Nat.div_mul_le_self (K*(R*C)) B
  nlinarith

/-- Every successful prefix of distribution has the claimed actual buffer
occupancy. Disk blocks themselves are not counted as resident payload. -/
theorem distribution_buffers (B n offset : ℕ) (bound : offset+n ≤ K*(R*C))
    (source finalSource : Reader Value) (buckets finalBuckets : Fin K → Writer Value)
    (hs : source.Valid B) (hb : ∀ k, (buckets k).Valid B)
    (hdone : distribute (sourceKey (R := R) (C := C)) B n offset bound source buckets =
      some (finalSource,finalBuckets)) :
    finalSource.pending.length+writerOccupancy finalBuckets ≤ (K+2)*B :=
  distribute_prefix_memory sourceKey B n offset bound source finalSource buckets finalBuckets hs hb hdone

/-- The same data-buffer bound holds during reconstruction, including the inverse pass. It counts the buffers that hold stream values. 
-/
theorem reconstruction_buffers (schedule : Fin (K*(R*C)) → Fin K)
    (B n offset : ℕ) (bound : offset+n ≤ K*(R*C))
    (readers finalReaders : Fin K → Reader Value) (writer finalWriter : Writer Value)
    (hr : ∀ k, (readers k).Valid B) (hw : writer.Valid B)
    (hdone : reconstruct schedule B n offset bound readers writer = some (finalReaders,finalWriter)) :
    occupiedReaders finalReaders+finalWriter.pending.length ≤ (K+2)*B :=
  reconstruct_prefix_memory schedule B n offset bound readers finalReaders writer finalWriter hr hw hdone

section RecursiveLayout
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Address
noncomputable section

abbrev segmentVolume (f G S : ℕ) :=
  (((radix^f)^Parameters.m)*G)*(((radix^f)^Parameters.m)*S)

theorem local_volume (f R G S : ℕ) :
    longVolume f R G S = R*segmentVolume f G S := by
  unfold longVolume segmentVolume
  ring

theorem parent_volume (f R G S : ℕ) :
    longVolume f (R*Parameters.W) G S = Parameters.W*(R*segmentVolume f G S) := by
  unfold longVolume segmentVolume
  ring

def segmentCode {P : ℕ} (f G S : ℕ)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    Fin (segmentVolume f G S) :=
  finProdFinEquiv (finProdFinEquiv (lexLayout (fieldVector f a.high),a.gap),
    finProdFinEquiv (lexLayout (fieldVector f a.low),a.suffix))

/-- The cyclic prefix remainder is exactly the role number; neither scalar
fields nor spectator coordinates move within a role file. -/
theorem parent_encoded (f R G S : ℕ)
    (a : LongAddress (Prefix := Fin (R*Parameters.W)) (Gap := Fin G) (Suffix := Fin S) f) :
    finCongr (parent_volume f R G S) (commonLayout f (R*Parameters.W) G S a) =
      sourceCode (a.prefixCoord.divNat,a.prefixCoord.modNat,segmentCode f G S a) := by
  have hprefix := congrArg Fin.val (finProdFinEquiv.apply_symm_apply a.prefixCoord)
  change a.prefixCoord.modNat.val+Parameters.W*a.prefixCoord.divNat.val = a.prefixCoord.val at hprefix
  apply Fin.ext
  simp only [finCongr_apply_coe,sourceCode,Equiv.trans_apply,commonLayout_val,
    tripleEncode_val,segmentCode,finProdFinEquiv_apply_val]
  rw [← hprefix]
  unfold segmentVolume
  ring

theorem local_encoded (f R G S : ℕ)
    (a : LongAddress (Prefix := Fin R) (Gap := Fin G) (Suffix := Fin S) f) :
    finCongr (local_volume f R G S) (commonLayout f R G S a) =
      finProdFinEquiv (a.prefixCoord,segmentCode f G S a) := by
  apply Fin.ext
  simp only [finCongr_apply_coe,commonLayout_val,segmentCode,finProdFinEquiv_apply_val]
  unfold segmentVolume
  ring

/-- Exact address correspondence with the recursive paper construction.
This identifies the executed disk permutation with `splitPrefix`, including
both canonical file layouts, rather than merely proving a similar transpose. -/
theorem splitPrefix_same_address (f R G S : ℕ)
    (a : LongAddress (Prefix := Fin (R*Parameters.W)) (Gap := Fin G) (Suffix := Fin S) f) :
    rolePermutation (finCongr (parent_volume f R G S)
      (commonLayout f (R*Parameters.W) G S a)) =
      finProdFinEquiv (roleEnumeration ((splitPrefix f) a).1,
        finCongr (local_volume f R G S) (commonLayout f R G S ((splitPrefix f) a).2)) := by
  rw [parent_encoded,permutation_encoded,local_encoded]
  simp only [splitPrefix,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
  rfl

def parentLayout (f R G S : ℕ) :=
  (commonLayout f (R*Parameters.W) G S).trans (finCongr (parent_volume f R G S))

def localLayout (f R G S : ℕ) :=
  (commonLayout f R G S).trans (finCongr (local_volume f R G S))

theorem splitPrefix_same_inverse (f R G S : ℕ) (r : Fin Parameters.W)
    (i : Fin (R*segmentVolume f G S)) :
    (parentLayout f R G S).symm (rolePermutation.symm (finProdFinEquiv (r,i))) =
      (splitPrefix f).symm (roleEnumeration.symm r,(localLayout f R G S).symm i) := by
  apply (parentLayout f R G S).injective
  apply rolePermutation.injective
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  change _ = rolePermutation (finCongr (parent_volume f R G S)
    (commonLayout f (R*Parameters.W) G S _))
  rw [splitPrefix_same_address]
  simp only [Equiv.apply_symm_apply]
  change _ = finProdFinEquiv (r,(localLayout f R G S) ((localLayout f R G S).symm i))
  rw [Equiv.apply_symm_apply]

theorem roleValues_splitInput (f R G S : ℕ)
    (F : LongAddress (Prefix := Fin (R*Parameters.W)) (Gap := Fin G) (Suffix := Fin S) f → Circuit.Bit)
    (r : Fin Parameters.W) :
    roleValues (F ∘ (parentLayout f R G S).symm) r =
      List.ofFn (splitInput f F (roleEnumeration.symm r) ∘ (localLayout f R G S).symm) := by
  unfold roleValues
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,splitPrefix_same_inverse,splitInput]

private theorem represented_cast {Addr : Type} {V N : ℕ} (layout : Addr ≃ Fin V)
    (h : V=N) (B : ℕ) (hB : 0 < B) (F : Addr → Circuit.Bit) :
    PhysicalRecursiveExchange.represented (layout.trans (finCongr h)) B hB F =
      PhysicalRecursiveExchange.represented layout B hB F := by
  subst N
  rfl

/-- The runtime scatter returns precisely the input files required by the
physical network, in roleEnumeration order. Its source is the same canonical
parent file used by the outer scalar scans. -/
theorem recursive_scatter_execution (f R G S B : ℕ) (hB : 0 < B)
    (F : LongAddress (Prefix := Fin (R*Parameters.W)) (Gap := Fin G) (Suffix := Fin S) f → Circuit.Bit) :
    ∃ cost,
      scatterRoles R Parameters.W (segmentVolume f G S) B
        (PhysicalRecursiveExchange.represented (commonLayout f (R*Parameters.W) G S) B hB F) =
        some (List.ofFn (fun r : Fin Parameters.W =>
          PhysicalRecursiveExchange.represented (commonLayout f R G S) B hB
            (splitInput f F (roleEnumeration.symm r))),cost) ∧
      cost*B ≤ 6*(Parameters.W*(R*segmentVolume f G S))+(3*Parameters.W+3)*B := by
  let source := F ∘ (parentLayout f R G S).symm
  obtain ⟨cost,hactual,hcost⟩ := scatterRoles_correct source B hB
  have hs : pack B hB (inputValues source) =
      PhysicalRecursiveExchange.represented (commonLayout f (R*Parameters.W) G S) B hB F := by
    rw [inputValues,← List.ofFn_eq_map]
    exact represented_cast (commonLayout f (R*Parameters.W) G S) _ B hB F
  have ht : (rolePieces source).map (pack B hB) =
      List.ofFn (fun r : Fin Parameters.W =>
        PhysicalRecursiveExchange.represented (commonLayout f R G S) B hB
          (splitInput f F (roleEnumeration.symm r))) := by
    simp only [rolePieces,List.map_ofFn]
    apply congrArg List.ofFn
    funext r
    simp only [Function.comp_apply,source,roleValues_splitInput]
    exact represented_cast (commonLayout f R G S) _ B hB _
  rw [hs,ht] at hactual
  refine ⟨cost,hactual,?_⟩
  exact (Nat.mul_le_mul_right B hcost).trans (partition_cost_bound source B hB)

/-- Physical collection uses exactly the role files just specified and
returns the original parent layout, including its block boundaries. -/
theorem recursive_gather_execution (f R G S B : ℕ) (hB : 0 < B)
    (F : LongAddress (Prefix := Fin (R*Parameters.W)) (Gap := Fin G) (Suffix := Fin S) f → Circuit.Bit) :
    ∃ cost,
      gatherRoles R Parameters.W (segmentVolume f G S) B
        (List.ofFn (fun r : Fin Parameters.W =>
          PhysicalRecursiveExchange.represented (commonLayout f R G S) B hB
            (splitInput f F (roleEnumeration.symm r)))) =
        some (PhysicalRecursiveExchange.represented (commonLayout f (R*Parameters.W) G S) B hB F,cost) ∧
      cost*B ≤ 6*(Parameters.W*(R*segmentVolume f G S))+(3*Parameters.W+3)*B := by
  let source := F ∘ (parentLayout f R G S).symm
  obtain ⟨cost,hactual,hcost⟩ := gatherRoles_correct source B hB
  have hs : pack B hB (inputValues source) =
      PhysicalRecursiveExchange.represented (commonLayout f (R*Parameters.W) G S) B hB F := by
    rw [inputValues,← List.ofFn_eq_map]
    exact represented_cast (commonLayout f (R*Parameters.W) G S) _ B hB F
  have ht : (rolePieces source).map (pack B hB) =
      List.ofFn (fun r : Fin Parameters.W =>
        PhysicalRecursiveExchange.represented (commonLayout f R G S) B hB
          (splitInput f F (roleEnumeration.symm r))) := by
    simp only [rolePieces,List.map_ofFn]
    apply congrArg List.ofFn
    funext r
    simp only [Function.comp_apply,source,roleValues_splitInput]
    exact represented_cast (commonLayout f R G S) _ B hB _
  rw [hs,ht] at hactual
  refine ⟨cost,hactual,?_⟩
  have hb := partition_cost_bound source B hB
  have hm := Nat.mul_le_mul_right B hcost
  nlinarith

/-- Gathering accepts arbitrary completed network output streams, not only
files unchanged since scatter. This is the interface needed after the eager
network has evaluated its crossed sink demands. -/
theorem recursive_gather_output_execution (f R G S B : ℕ) (hB : 0 < B)
    (output : Reg → LongAddress (Prefix := Fin R) (Gap := Fin G) (Suffix := Fin S) f → Circuit.Bit) :
    ∃ cost,
      gatherRoles R Parameters.W (segmentVolume f G S) B
        (List.ofFn (fun r : Fin Parameters.W =>
          PhysicalRecursiveExchange.represented (commonLayout f R G S) B hB
            (output (roleEnumeration.symm r)))) =
        some (PhysicalRecursiveExchange.represented (commonLayout f (R*Parameters.W) G S) B hB
          (gatherOutput f output),cost) ∧
      cost*B ≤ 6*(Parameters.W*(R*segmentVolume f G S))+(3*Parameters.W+3)*B := by
  have hsplit : splitInput f (gatherOutput f output) = output := by
    funext r a
    simp only [splitInput,gatherOutput,Equiv.apply_symm_apply]
  simpa only [hsplit] using recursive_gather_execution f R G S B hB (gatherOutput f output)

end
end RecursiveLayout

end CSL.PhysicalRolePartition
end PhysicalRolePartition

section WordAlignment
/-! Literal word alignment of the sorting exchange layouts. A suffix word
and a bit position use the ordinary consecutive-bit encoding; changing the
address fields or distributing prefix roles leaves that bit position intact.
These are address equalities, not an uncharged disk permutation. -/
set_option autoImplicit false
namespace CSL.CommonWordAlignment
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open TriangularStreams PhysicalRolePartition
noncomputable section

def suffixBit {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin (S*w)) f :=
  ⟨a.prefixCoord,a.high,a.gap,a.low,finProdFinEquiv (a.suffix,b)⟩

theorem volume_word (f P G S w : ℕ) :
    longVolume f P G S * w = longVolume f P G (S*w) := by
  unfold longVolume
  ring

theorem segmentVolume_word (f G S w : ℕ) :
    segmentVolume f G (S*w) = segmentVolume f G S * w := by
  unfold segmentVolume
  ring

/-- The numeric bit address is precisely the word address times the word
width, plus the original bit offset. -/
theorem commonLayout_word_val {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    (commonLayout f P G (S*w) (suffixBit a b)).val =
      (commonLayout f P G S a).val*w+b.val := by
  simp only [commonLayout_val,suffixBit,finProdFinEquiv_apply_val]
  ring

theorem commonLayout_word {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    commonLayout f P G (S*w) (suffixBit a b) =
      finCongr (volume_word f P G S w)
        (finProdFinEquiv (commonLayout f P G S a,b)) := by
  apply Fin.ext
  rw [commonLayout_word_val]
  simp only [finCongr_apply_coe,finProdFinEquiv_apply_val]
  ring

theorem commonLayout_word_mod {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    (commonLayout f P G (S*w) (suffixBit a b)).val % w = b.val := by
  rw [commonLayout_word_val]
  simp [Nat.add_mod,Nat.mod_eq_of_lt b.isLt]

theorem commonLayout_word_div {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    (commonLayout f P G (S*w) (suffixBit a b)).val / w =
      (commonLayout f P G S a).val := by
  have hw : 0 < w := lt_of_le_of_lt (Nat.zero_le b.val) b.isLt
  rw [commonLayout_word_val]
  simp [Nat.add_div,Nat.div_eq_of_lt b.isLt,hw]
  exact Nat.mod_lt _ hw

theorem exchange_word {f P G S w : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) : exchange (suffixBit a b) = suffixBit (exchange a) b := rfl

set_option maxRecDepth 100000 in
theorem coordinatePermutation_word {f P G S w : ℕ} (e : Edge)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    coordinatePermutation f e (suffixBit a b) =
      suffixBit (coordinatePermutation f e a) b := by
  simp only [RecursiveExchange.coordinatePermutation, Equiv.coe_fn_mk, RecursiveExchange.beforeCoordinates, suffixBit]

set_option maxRecDepth 100000 in
theorem coordinatePermutation_inverse_word {f P G S w : ℕ} (e : Edge)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    (coordinatePermutation f e).symm (suffixBit a b) =
      suffixBit ((coordinatePermutation f e).symm a) b := by
  simp only [RecursiveExchange.coordinatePermutation, Equiv.coe_fn_symm_mk, RecursiveExchange.afterCoordinates, suffixBit]

theorem splitPrefix_word {f R G S w : ℕ}
    (a : LongAddress (Prefix := Fin (R*Parameters.W))
      (Gap := Fin G) (Suffix := Fin S) f) (b : Fin w) :
    splitPrefix f (suffixBit a b) =
      ((splitPrefix f a).1,suffixBit (splitPrefix f a).2 b) := rfl

theorem splitPrefix_inverse_word {f R G S w : ℕ} (r : Reg)
    (a : LongAddress (Prefix := Fin R) (Gap := Fin G) (Suffix := Fin S) f)
    (b : Fin w) :
    (splitPrefix f).symm (r,suffixBit a b) =
      suffixBit ((splitPrefix f).symm (r,a)) b := rfl

/-- The cast only reassociates the same number of bit positions. -/
def roleBitIndex {R K C w : ℕ} (x : Fin (K*(R*C))) (b : Fin w) :
    Fin (K*(R*(C*w))) :=
  finCongr (by ring : K*(R*C)*w = K*(R*(C*w))) (finProdFinEquiv (x,b))

theorem roleBitIndex_val {R K C w : ℕ} (x : Fin (K*(R*C))) (b : Fin w) :
    (roleBitIndex x b).val = x.val*w+b.val := by
  simp only [roleBitIndex,finCongr_apply_coe,finProdFinEquiv_apply_val]
  ring

theorem sourceCode_word {R K C w : ℕ} (a : TripleAddress R K C) (b : Fin w) :
    sourceCode (a.1,a.2.1,finProdFinEquiv (a.2.2,b)) =
      roleBitIndex (sourceCode a) b := by
  apply Fin.ext
  simp only [sourceCode,Equiv.trans_apply,finCongr_apply_coe,
    tripleEncode_val,finProdFinEquiv_apply_val,roleBitIndex_val]
  ring

/-- Role transposition moves complete words, preserving every bit offset. -/
theorem rolePermutation_word {R K C w : ℕ}
    (x : Fin (K*(R*C))) (b : Fin w) :
    rolePermutation (roleBitIndex x b) =
      roleBitIndex (rolePermutation x) b := by
  obtain ⟨a,rfl⟩ := sourceCode.surjective x
  rw [← sourceCode_word,permutation_encoded,permutation_encoded]
  apply Fin.ext
  simp only [tripleEncode_val,finProdFinEquiv_apply_val,roleBitIndex_val]
  ring

theorem rolePermutation_inverse_word {R K C w : ℕ}
    (x : Fin (K*(R*C))) (b : Fin w) :
    rolePermutation.symm (roleBitIndex x b) =
      roleBitIndex (rolePermutation.symm x) b := by
  apply rolePermutation.injective
  rw [Equiv.apply_symm_apply,rolePermutation_word,Equiv.apply_symm_apply]

/-- View the same role-layout words as consecutive bits. The cast changes
only multiplication parentheses, so it changes no physical position. -/
def roleBits {R K C w : ℕ} (F : Fin (K*(R*C)) → WordControl.Word w) :
    Fin (K*(R*(C*w))) → Circuit.Bit :=
  fun x => BitWordPacking.blockBits (K*(R*C)) w F
    (finCongr (by ring : K*(R*(C*w)) = K*(R*C)*w) x)

theorem roleBits_at {R K C w : ℕ}
    (F : Fin (K*(R*C)) → WordControl.Word w) (x : Fin (K*(R*C))) (b : Fin w) :
    roleBits F (roleBitIndex x b) = BitWordPacking.wordBits w (F x) b := by
  have h : finCongr (by ring : K*(R*(C*w)) = K*(R*C)*w)
      (roleBitIndex x b) = finProdFinEquiv (x,b) := by
    apply Fin.ext
    rfl
  unfold roleBits
  rw [h,BitWordPacking.blockBits_at]

/-- The bit file assigned to a role is exactly the bit encoding of the word
file assigned to that role, including its original within-word bit order. -/
theorem roleValues_bits {R K C w : ℕ}
    (F : Fin (K*(R*C)) → WordControl.Word w) (r : Fin K) :
    roleValues (roleBits F) r =
      List.ofFn (BitWordPacking.blockBits (R*C) w
        (fun p => F (rolePermutation.symm (finProdFinEquiv (r,p))))) := by
  unfold roleValues
  rw [List.ofFn_congr (show R*(C*w) = (R*C)*w by ring)]
  apply congrArg List.ofFn
  funext i
  obtain ⟨⟨p,b⟩,rfl⟩ := finProdFinEquiv.surjective i
  have h : finProdFinEquiv
      (r,Fin.cast (show (R*C)*w = R*(C*w) by ring) (finProdFinEquiv (p,b))) =
      roleBitIndex (finProdFinEquiv (r,p)) b := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val,Fin.coe_cast,roleBitIndex_val]
    ring
  rw [h,rolePermutation_inverse_word,roleBits_at,BitWordPacking.blockBits_at]

end
end CSL.CommonWordAlignment
end WordAlignment


