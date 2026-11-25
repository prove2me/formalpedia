-- Prove2me | Definitions.Def_DetDLP_W3C_FpStep
-- name    : DetDLP_W3C_FpStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:29:06.892964+00:00
-- url     : https://prove2.me/theorems/8dd7c521-3cf3-44c0-9b9b-9bd4b967de9e
-- title:
--   Finite-field Stage-II PolyT controller step
-- statement:
--   **State and query interface.** The controller stores seven binary counters and five word fields. Its twelve-frame encoding satisfies $\operatorname{unpackState}(\operatorname{packState}(s))=s$. Both maps are polynomial-time operations. For every $j\in\operatorname{Fin}(9)$, `queryInput` constructs the corresponding oracle payload. The separator receives the labels from the affine representative, whereas the contraction oracle receives the network packet unchanged.
--
--   **Initial rounds.** Write $M=p-1$. When $\neg\,\mathrm{w3\_large}(p,M)$, a scan call followed by a halting round returns the oracle answer. The lemma `scan_loop` gives the two-round trace and its word-length bound. In the large case the controller requests a seed plan and then enumeration of its native factor blocks. Subsequent Stage-II rounds are represented by a continuation: `step resume` is polynomial-time whenever `resume` is polynomial-time.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_BlockLookup
import Definitions.Def_DetDLP_W3C_NineOracleLoop
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.W3C.FpStep
open NineOracleLoop Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.fst PolyT.snd PolyT.prodMk PolyT.const PolyT.id' PolyT.getD PolyT.flatten PolyT.length
  PolyT.map PolyT.flatMap PolyT.mul PolyT.div w5_M6Sort.cw_poly w5_M6Sort.encode_poly w5_M6Sort.decode_poly
  first_poly more_poly frame_poly S8G.FpMoment.Code.width_poly P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
variable {α : Type} [Enc α]
private def groupSize (p : ℕ) := p-1
@[local fun_prop] private theorem sizeP {p : α → ℕ} (h : PolyT p) : PolyT fun x => groupSize (p x) := PolyT.sub h (PolyT.const 1)
@[local fun_prop] private theorem encP {f : α → List W} (h : PolyT f) : PolyT fun x => Encoding.encodeList id (f x) := by
  have flat (l : List W) : Encoding.encodeList id l = l.flatMap (fun u => true :: frame u) ++ [false] := by
    induction l with | nil => rfl | cons w l ih => simp [Encoding.encodeList, ih, List.flatMap, List.append_assoc]
  simp only [flat]; fun_prop
private def splitInput (w : W) := (first (true::w),more (true::w))
private theorem split_pair (s a : W) : splitInput (pairWord s a) = (s,a) := by
  have run (x acc : W) : ∀ f : W, x.length ≤ f.length → f.foldl advance (acc,Encoding.frame x ++ a) = (x.reverse ++ acc,false::a) := by
    induction x generalizing acc with
    | nil => intro f _; induction f <;> simp_all [Encoding.frame,advance,List.foldl]
    | cons b x ih => intro f h; cases f with
      | nil => simp at h
      | cons k f => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) f (by simpa using h)
  have h (x : W) : x.length ≤ (Encoding.frame x).length := by induction x <;> simp_all [Encoding.frame]; omega
  change (first (true::(frame s ++ a)),more (true::(frame s ++ a))) = _
  rw [frame_correct]; simp only [first,more,parse,List.tail_cons]; rw [run s [] _ (by simp only [List.length_cons,List.length_append]; have := h s; omega)]; simp
def seedNatWord (b : ℕ) (w : W) := encodeNatListBin (((List.range w.length).take (w.length/b)).map
  fun i => PolyT.bval (((w.drop (i*b)).take b).reverse))
@[local fun_prop] private theorem seedP {b : α → ℕ} {w : α → W} (hb : PolyT b) (hw : PolyT w) :
    PolyT fun x => seedNatWord (b x) (w x) := by
  have hr : PolyT fun x => List.range (w x).length := PolyT.range (Unary.of_length hw)
  unfold seedNatWord; fun_prop
/-- Seven binary counters followed by the native plan, blocks, representative, scratch packet, and prefix. -/
structure FpState where
  (phase p g a T idx fuel : ℕ)
  (planWord blocksWord repWord pktWord pre : W)
  deriving DecidableEq, Repr
def fields (s : FpState) : List W := [countWord s.phase, countWord s.p, countWord s.g, countWord s.a,
  countWord s.T, countWord s.idx, countWord s.fuel, s.planWord, s.blocksWord, s.repWord, s.pktWord, s.pre]
instance : Enc FpState := ⟨fun s => Enc.toV (fields s)⟩
def packState (s : FpState) := Encoding.encodeList id (fields s)
def unpackState (w : W) : FpState :=
  let f := BlockLookup.decodeFrames w; let n := fun i => PolyT.bval (f.getD i [])
  ⟨n 0,n 1,n 2,n 3,n 4,n 5,n 6,f.getD 7 [],f.getD 8 [],f.getD 9 [],f.getD 10 [],f.getD 11 []⟩
@[simp] theorem unpackState_packState (s : FpState) : unpackState (packState s) = s := by
  cases s; simp [packState,unpackState,fields]
@[fun_prop] theorem packState_poly : PolyT packState := by
  apply encP; obtain ⟨P,c,r,h⟩ := PolyT.id' (α := List W)
  exact ⟨P,c,fun s => r (fields s),fun s => h (fields s)⟩
@[fun_prop] theorem unpackState_poly : PolyT unpackState := by
  change PolyT fun w => fields (unpackState w); unfold fields unpackState; dsimp only; fun_prop
/-- Prove a bound on typed states by working on their words. -/
theorem onState {β : Type} [Enc β] {f : FpState → β} (h : PolyT fun w => f (unpackState w)) : PolyT f := (h.comp packState_poly).congr fun s => by simp
/-- The five separator fields; the fourth holds labels, not the entire coset packet. -/
def fpQueryInput (p g M T : ℕ) (seed blocks labels pre : W) :=
  Encoding.encodeList id [encodeNatListBin [p,g,M,T],seed,blocks,labels,pre]
@[fun_prop] theorem fpQueryInput_poly {p g M T : α → ℕ} {seed blocks labels pre : α → W}
    (hp : PolyT p) (hg : PolyT g) (hM : PolyT M) (hT : PolyT T) (hs : PolyT seed) (hb : PolyT blocks) (hl : PolyT labels) (hr : PolyT pre) :
    PolyT fun x => fpQueryInput (p x) (g x) (M x) (T x) (seed x) (blocks x) (labels x) (pre x) := by
  unfold fpQueryInput; fun_prop
/-- Slots 0–3 are scan, seed prepare, native enumerate and native decompose; 4–5 are
    the reference base calls; 6–8 are separator build, contract and HNF update.
    The HNF scratch packet has two fields: the reduced row and the binary right side. -/
def queryInput (j : Fin 9) (s : FpState) : W :=
  let xs := (BlockLookup.decodeBlocks s.blocksWord).flatten ++ [countWord s.g, countWord s.a]
  let px := encodeNatListBin [s.p, PolyT.bval (xs.getD s.idx [])]
  match j.val with
  | 0 => encodeFpDLPInput s.p s.g s.a  | 1 => countWord s.p
  | 2 => Encoding.encodeList id [countWord s.p, s.planWord]
  | 3 => Encoding.encodeList id [px, s.planWord]
  | 4 => countWord s.p  | 5 => px
  | 6 => fpQueryInput s.p s.g (groupSize s.p) s.T (seedNatWord (S8G.FpMoment.Code.width s.p)
      (second s.planWord.tail)) s.blocksWord (first s.repWord) s.pre
  | 7 => s.pktWord
  | _ => NewtonPoly.updateWord (groupSize s.p) xs.length s.repWord (w5_M6Sort.decode (first s.pktWord))
      (PolyT.bval (second s.pktWord))
@[fun_prop] theorem queryInput_poly (j : Fin 9) : PolyT (queryInput j) := by
  apply onState; fin_cases j <;> dsimp [queryInput,unpackState,encodeFpDLPInput,second] <;> fun_prop
/-- The same state can be saved while a different state supplies the query operands. -/
def call (j : Fin 9) (save args : FpState) := false :: pairWord (packState save) (tag9 j (queryInput j args))
@[fun_prop] theorem call_poly (j : Fin 9) {s a : α → FpState} (hs : PolyT s) (ha : PolyT a) :
    PolyT fun x => call j (s x) (a x) := by
  unfold call; apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const false)
  change PolyT fun x => frame (packState (s x)) ++ tag9 j (queryInput j (a x))
  exact PolyT.append (frame_poly (packState_poly.comp hs)) ((tag9_poly j).comp ((queryInput_poly j).comp ha))
def start (k : ℕ) (w : W) : FpState := let n := w5_M6Sort.decode w
  ⟨k,n.getD 0 0,n.getD 1 0,n.getD 2 0,0,0,0,[],[],[],[],[]⟩
@[local fun_prop] theorem start_poly (k : ℕ) : PolyT (start k) := by
  change PolyT fun w => fields (start k w); unfold fields start; dsimp only; fun_prop
def entry (w : W) := let p := (w5_M6Sort.decode w).getD 0 0
  if NewtonPoly.largeCheck p (groupSize p) then call 1 (start 2 w) (start 2 w) else call 0 (start 1 w) (start 1 w)
@[fun_prop] theorem entry_poly : PolyT entry := by unfold entry; fun_prop
def prepared (z : W × W) : FpState := let plan := second z.2
  {unpackState z.1 with phase := 3, planWord := plan, T := PolyT.bval (first plan.tail)}
@[fun_prop] theorem prepared_poly : PolyT prepared := by
  change PolyT fun z => fields (prepared z); unfold fields prepared unpackState second; dsimp only; fun_prop
/-- After enumerating the native blocks the remaining Stage-II transitions belong to `resume`.
    State and last answer are passed separately; the scan answer is returned without recoding. -/
def step (resume : W × W → W) (input : W) :=
  let z := splitInput input; let fs := BlockLookup.decodeFrames z.1; let k := PolyT.bval (fs.getD 0 [])
  if fs.length = 3 then entry z.1 else if k = 1 then true :: z.2 else if k = 2 then
    call 2 (prepared z) (prepared z) else resume z
@[fun_prop] theorem step_poly {resume : W × W → W} (h : PolyT resume) : PolyT (step resume) := by
  unfold step splitInput; fun_prop
@[simp] theorem step_entry (resume : W × W → W) (p g a : ℕ) :
    step resume (pairWord (encodeFpDLPInput p g a) []) = entry (encodeFpDLPInput p g a) := by
  rw [step,split_pair]; simp [encodeFpDLPInput,encodeNatListBin]
@[simp] theorem step_saved (resume : W × W → W) (s : FpState) (ans : W) :
    step resume (pairWord (packState s) ans) =
      (if s.phase = 1 then true :: ans else if s.phase = 2 then
        call 2 (prepared (packState s,ans)) (prepared (packState s,ans)) else resume (packState s,ans)) := by
  rw [step,split_pair]; simp [packState,fields]
/-- A bounded scan call followed by its unmodified answer is a complete two-round trace. -/
theorem scan_loop (resume : W × W → W) (R : W → W → Prop) (p g a : ℕ) (y : W)
    (small : ¬w3_large p (p-1)) (hy : R (tag9 0 (encodeFpDLPInput p g a)) y) :
    let w := encodeFpDLPInput p g a; let s := packState (start 1 w); let q := tag9 0 w
    LoopRuns (step resume) R 2 w [] y ((pairWord w []).length + (pairWord s q).length + (pairWord s y).length + y.length) := by
  let w := encodeFpDLPInput p g a
  have hs : NewtonPoly.largeCheck p (p-1) = false := by
    cases e : NewtonPoly.largeCheck p (p-1) <;> simp_all [NewtonPoly.largeCheck_correct]
  have he : entry w = call 0 (start 1 w) (start 1 w) := by simp [w,entry,groupSize,encodeFpDLPInput,hs]
  have hq : queryInput 0 (start 1 w) = w := by simp [w,queryInput,start,encodeFpDLPInput]
  refine Or.inr ⟨packState (start 1 w),tag9 0 w,y,?_,by omega,by dsimp only [w]; omega,by omega,hy,
    Or.inl ⟨?_,by dsimp only [w]; omega,by omega⟩⟩
  · rw [step_entry,←show encodeFpDLPInput p g a = w from rfl,he,call,hq]
  · rw [step_saved]; rfl
end DetDLP.W3C.FpStep


