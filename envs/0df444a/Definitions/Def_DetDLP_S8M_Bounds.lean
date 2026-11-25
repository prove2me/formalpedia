-- Prove2me | Definitions.Def_DetDLP_S8M_Bounds
-- name    : DetDLP_S8M_Bounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:34:53.527752+00:00
-- url     : https://prove2.me/theorems/c121e069-5458-4fb2-a361-82b644049991
-- title:
--   Tag 6 EC pair-collision degree, budget, and realizes_of_eval
-- statement:
--   **Degree and size.** Let $p>3$ be prime, let $E/\mathbb F_p$ be an elliptic curve, and write $b=\operatorname{bitLen}(p)$. For $m\geq 1$ and a prefix $\eta$ of length at most $2m(2b+1)$, set $s=4{,}000{,}000\,m(b+2)$. If $n_e$ and $n_g$ denote the numbers of incidences and gates in the Tag 6 layout, then
--
--   $$2n_e<s,\qquad n_g\leq s,\qquad \deg(v)\leq\max\!\left\{12,\left\lceil136(b+2)^{3/4}\right\rceil\right\}.$$
--
--   The degree bound holds at every vertex of the factor graph before subdivision. The size estimate counts $2m$ atom blocks, $2m$ coordinate conversions, and $2m-1$ elliptic-curve additions, together with the target and prefix checks, the anchors, and the copy cycles.
--
--   **Realization.** Take $m=\operatorname{blockCount}(b)$ and $T\leq p$. If `make` encodes the specified subdivided instance and `port` returns the prescribed tensor entry at every port query, then `realizes_of_eval` establishes `Realizes` with parameter $16{,}000{,}000$. Its value is the number of ordered pairs of point tuples $(P,Q)$ for which $P_i$ and $Q_i$ lie in the designated factor block at each index, the interleaved encoding begins with $\eta$, and $\sum_i(P_i+Q_i)=X$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_Semantics
import Definitions.Def_DetDLP_S8I_ECPairPredicate
import Definitions.Def_DetDLP_S8J_CircuitRealizes

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2400000

namespace DetDLP.S8M.Bounds
open S8H0 S8H0.NamedBlocks S8H0.GraphDegree S8J S8J.CircuitRealizes S8C Groundwork S8H
open S8H0.RegisterMap S8H0.RangeRows S8H0.HashRows S8H0.GateRoutes S8N
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
open private ranges maskEq from Definitions.Def_DetDLP_S8M_ECMapRows
open private invRows selectRows from Definitions.Def_DetDLP_S8N_ECAddRoutes
open private foldStep from Definitions.Def_DetDLP_S8M_ECFoldRoutes
attribute [-simp] Fin.natAdd_eq_addNat

/-- Size field of the Tag 6 packet for `m` block positions and `b` modulus bits. -/
abbrev scale (m b : ℕ) := 4000000*m*(b+2)

private abbrev cost {k : ℕ} (b : B k) := b.core.A.ne + b.core.A.ng

private theorem cost_rename {k l : ℕ} (b : B k) (r : Fin b.core.A.ne → Fin l) :
    cost (⟨b.core,r⟩ : B l) = cost b := rfl

private theorem cost_join {k : ℕ} (u v : B k) : cost (joinB u v) = cost u + cost v := by
  simp only [cost,joinB,join]; omega

private theorem cost_rows {s : RegisterMap.Shape} (n k : ℕ) (r : Fin n → Fin k → Ref s)
    (t : Fin n → (Fin k → Bool) → Bool) : cost (rows n k r t) = n*k+n := rfl
private theorem cost_add {s : RegisterMap.Shape} {n : ℕ} (c : Bool) (a b z k : Fin n → Ref s) :
    cost (NamedBlocks.add c a b z k) = n*5+n := rfl
private theorem cost_checker {s : RegisterMap.Shape} {d : ℕ} (p : ℕ) (a : Path (triple d) s) :
    cost (checker p a) = (d+1)*5+(d+1) := rfl

private theorem many_count {k n C : ℕ} (f : Fin (n+1) → B k) (h : ∀ i, cost (f i) ≤ C) :
    cost (many n f) ≤ (n+1)*C := by
  induction n with
  | zero => simpa [many] using h 0
  | succ n ih =>
    have ht := ih (fun j => f j.succ) (fun j => h j.succ)
    have hi := h 0
    rw [many,cost_join,Nat.succ_mul]; omega

private theorem count {s : RegisterMap.Shape} {n C : ℕ} (f : Fin n → B (s.size+1))
    (h : ∀ i, cost (f i) ≤ C) : cost (S8G.SeedAndAtomBank.allRows n f) ≤ n*C := by
  cases n with
  | zero => simp [S8G.SeedAndAtomBank.allRows,cost_rows]
  | succ n => exact many_count _ h

private theorem hash_count {s : RegisterMap.Shape} {d : ℕ} (hd : 1 ≤ d) (p : ℕ) (w : Wires d hd s) :
    cost (HashRows.block p w) ≤ 5000*(d+1) := by
  have he := w4_M5GraphBounds.graph_edge_bound hd
  have hv := GraphBudget.baseV hd
  simp only [HashRows.block,HashRows.product,HashRows.sumRows,eqs,cost_join,cost_rows,cost_add,
    cost,mapped,w3_fpMulLayout,w3_m5Layout,w3_forgetSides]
  omega

private theorem range_count (d e p : ℕ) : cost (RangeRows.block d e p) ≤ 96*(d+1) := by
  simp only [RangeRows.block,many,cost_join,cost_checker]; omega

private theorem atom_cost {d m : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) (S : Routes.SeedData m)
    (i : Fin (2*m)) : cost (Routes.atomRows hd p T c S i) ≤ 36000*(d+1) := by
  have h6 := many_count (fun g : Fin 6 => HashRows.block p (GateRoutes.wires hd p c g.castSucc))
    (fun g => hash_count hd p _)
  have h1 := hash_count hd p (S8H4.Routes.network.six hd p c)
  have hr := range_count d (Routes.G hd) p
  simp only [Routes.atomRows,ECAtomSlot.slotBlock,fixed,cost_join,cost_rename,CurveRows.block,
    cost_rows,cost_add]
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hr (Nat.add_le_add h6 (le_refl _)))
    (Nat.add_le_add h1 (le_refl _))) (le_refl _)).trans ?_
  omega

private theorem map_cost {s : RegisterMap.Shape} {d e : ℕ} (hd : 1 ≤ d) (p b2 a1 a3 : ℕ)
    (f : Ref s) (x y : Word s) (q : Path (ECMapRows.mapShape d e) s) :
    cost (ECMapRows.mapBlock hd p b2 a1 a3 f x y q) ≤ 21000*(d+1) := by
  have hash4 (w : Fin 4 → Wires d hd s) := many_count (fun i => HashRows.block p (w i))
    (fun i => hash_count hd p _)
  simp only [ECMapRows.mapBlock,ranges,maskEq,eqs,cost_join,cost_rows]
  refine (Nat.add_le_add (le_refl _) (Nat.add_le_add (hash4 _) (le_refl _))).trans ?_
  simp only [many,cost_join,cost_checker]; omega

private theorem add_cost {s : RegisterMap.Shape} {d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (f : Ref s) (x y : Word s) (g : Ref s) (X Y : Word s) (q : Path (ECAddRoutes.addShape d e) s) :
    cost (ECAddRoutes.addBlock hd p neg1 three c4 f x y g X Y q) ≤ 76000*(d+1) := by
  have hash15 (w : Fin 15 → Wires d hd s) := many_count (fun i => HashRows.block p (w i))
    (fun i => hash_count hd p _)
  simp only [ECAddRoutes.addBlock,invRows,selectRows,cost_join,cost_rows]
  refine (Nat.add_le_add (le_refl _) (Nat.add_le_add (le_refl _) (Nat.add_le_add (hash15 _) (le_refl _)))).trans ?_
  simp only [many,cost_join,cost_checker]; omega

private theorem fold_cost {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (p neg1 three c4 : ℕ) (t : Routes.Target) :
    cost (Routes.foldRows hd hm p neg1 three c4 t) ≤ 3+6*d + (2*m)*(76000*(d+1)) := by
  simp only [Routes.foldRows,ECFoldRoutes.foldBlock,cost_join,cost_rows]
  calc
    _ ≤ 1*2+1 + (d*2+d + (d*2+d + (2*m-1)*(76000*(d+1)))) := by
      apply Nat.add_le_add_left
      apply Nat.add_le_add_left
      apply Nat.add_le_add_left
      apply count
      intro i
      exact add_cost hd p neg1 three c4 _ _ _ _ _ _ _
    _ ≤ _ := by
      have hle := Nat.mul_le_mul_right (76000*(d+1)) (Nat.sub_le (2*m) 1)
      omega

private theorem bank_size {m d : ℕ} (hd : 1 ≤ d) :
    (Routes.bank m d (Routes.G hd)).size ≤ (2*m)*(60000*(d+1)) := by
  have he := w4_M5GraphBounds.graph_edge_bound hd
  simp only [Routes.bank,RegisterMap.Shape.size]
  apply (Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le (2*m) 1)) _) _).trans
  rw [← Nat.mul_add,← Nat.mul_add]; apply Nat.mul_le_mul_left
  simp only [ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,ECMapRows.mapShape,
    ECAddRoutes.addShape,ECMapRows.slot,run,triple,RegisterMap.mul,GateRoutes.auxShape,RegisterMap.Shape.size,Routes.G]
  omega

variable {p m T : ℕ} [Fact p.Prime]
variable (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ m) (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool)

private theorem sizes (hη : η.length ≤ 2*m*(2*bitLen p+1)) :
    2*(Semantics.layout E hp hm S X η T).ne < scale m (bitLen p) ∧
      (Semantics.layout E hp hm S X η T).ng ≤ scale m (bitLen p) := by
  let d := GateSemantics.d p; let hd := GateSemantics.hd p
  let N := Semantics.net E hp hm S X η T
  have regs : (Semantics.shape p m).size ≤ (2*m)*(60000*(d+1)) := bank_size hd
  have a := count (Routes.atomRows hd p T (GateSemantics.coeff E) (Semantics.seed S))
    (fun i => atom_cost hd p T _ _ i)
  have b := count (Routes.mapRows (m:=m) hd p E.b₂.val E.a₁.val E.a₃.val)
    (fun i => map_cost hd p _ _ _ _ _ _ _)
  have c := fold_cost hd hm p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val (Semantics.target E hp X)
  have net : cost N ≤ 2 + (2*m)*(36000*(d+1)) + (2*m)*(21000*(d+1)) +
      (3+6*d+(2*m)*(76000*(d+1))) + 2*η.length := by
    simp only [N,Semantics.net,Semantics.rowsAt,Routes.networkAt,cost_join,Routes.prefixRows,cost_rows]
    change 2 + (_ + (_ + (_ + (η.length*1+η.length)))) ≤ _
    exact (Nat.add_le_add_left (Nat.add_le_add a (Nat.add_le_add b (Nat.add_le_add c (le_refl _)))) 2).trans (by dsimp only [d]; omega)
  change 2*((_+1+N.core.A.ne)+((_+1+N.core.A.ne)+(_+1+N.core.A.ne))) < _ ∧
    (_+1+N.core.A.ng)+(_+1+N.core.A.ne) ≤ _
  have hdle : d ≤ m*d := Nat.le_mul_of_pos_left d hm
  dsimp only [cost] at net
  dsimp only [d,GateSemantics.d,ECPointArithmetic.width,scale] at regs net hdle ⊢
  ring_nf at regs net hdle hη ⊢; constructor <;> omega

/-- Twice the number of incidences is strictly below the packet size field. -/
theorem edgeBudget (hη : η.length ≤ 2*m*(2*bitLen p+1)) :
    2*(Semantics.layout E hp hm S X η T).ne < scale m (bitLen p) :=
  (sizes E hp hm S X η hη).1

/-- The number of factor gates is at most the same size field. -/
theorem gateBudget (hη : η.length ≤ 2*m*(2*bitLen p+1)) :
    (Semantics.layout E hp hm S X η T).ng ≤ scale m (bitLen p) :=
  (sizes E hp hm S X η hη).2

private theorem all_ok {s : RegisterMap.Shape} {n D : ℕ} (f : Fin n → B (s.size+1))
    (h : ∀ i, good (f i) (cap D)) : good (S8G.SeedAndAtomBank.allRows n f) (cap D) := by
  cases n with
  | zero => exact mono (row_ok 0 0 _ _) (small D 0 (by decide))
  | succ n => exact many_ok n _ h

private theorem row_good {s : RegisterMap.Shape} {n k : ℕ} (p : ℕ) (hk : k ≤ 12)
    (r : Fin n → Fin k → Ref s) (t : Fin n → (Fin k → Bool) → Bool) : good (rows n k r t) (cap p) :=
  mono (row_ok n k r t) (small p k hk)

private theorem add_good {s : RegisterMap.Shape} {n : ℕ} (p : ℕ) (c : Bool) (a b z k : Fin n → Ref s) :
    good (NamedBlocks.add c a b z k) (cap p) := mono (add_ok c a b z k) (small p 5 (by decide))

private theorem hash_good {s : RegisterMap.Shape} (p : ℕ) (w : Wires (GateSemantics.d p) (GateSemantics.hd p) s) :
    good (HashRows.block p w) (cap p) := by
  unfold HashRows.block HashRows.product
  refine join_ok _ _ (join_ok _ _ (join_ok _ _ (mul_ok p _) ?_) (join_ok _ _ (mul_ok p _) ?_))
    (join_ok _ _ (add_good p _ _ _ _ _) (join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _)))
  all_goals exact row_good p (by decide) _ _

omit [Fact p.Prime] [E.IsElliptic] in
private theorem atom_good (i : Fin (2*m)) :
    good (Routes.atomRows (GateSemantics.hd p) p T (GateSemantics.coeff E) (Semantics.seed S) i) (cap p) := by
  have r : good (RangeRows.block (GateSemantics.d p) (GateSemantics.e p) p) (cap p) := by
    unfold RangeRows.block
    exact join_ok _ _ (join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _))
      (many_ok _ _ fun _ => join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _))
  unfold Routes.atomRows ECAtomSlot.slotBlock
  refine join_ok _ _ ?_ (row_good p (by decide) _ _)
  change good (fixed _ _ _ _) _
  unfold fixed
  refine join_ok _ _ ?_ (join_ok _ _ (hash_good p _) (join_ok _ _ (row_good p (by decide) _ _) (add_good p _ _ _ _ _)))
  exact join_ok _ _ r (join_ok _ _ (many_ok _ _ fun _ => hash_good p _) (row_good p (k:=5) (by decide) _ _))

private theorem map_good {s : RegisterMap.Shape} {e : ℕ} (p b2 a1 a3 : ℕ) (f : Ref s) (x y : Word s)
    (q : Path (ECMapRows.mapShape (GateSemantics.d p) e) s) :
    good (ECMapRows.mapBlock (GateSemantics.hd p) p b2 a1 a3 f x y q) (cap p) := by
  unfold ECMapRows.mapBlock ranges
  exact join_ok _ _ (join_ok _ _ (join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _))
    (many_ok _ _ fun _ => join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _)))
    (join_ok _ _ (many_ok _ _ fun _ => hash_good p _) (join_ok _ _ (row_good p (by decide) _ _)
      (join_ok _ _ (row_good p (by decide) _ _) (row_good p (by decide) _ _))))

private theorem add_block_good {s : RegisterMap.Shape} {e : ℕ} (p n t c : ℕ) (f : Ref s) (x y : Word s)
    (g : Ref s) (X Y : Word s) (q : Path (ECAddRoutes.addShape (GateSemantics.d p) e) s) :
    good (ECAddRoutes.addBlock (GateSemantics.hd p) p n t c f x y g X Y q) (cap p) := by
  unfold ECAddRoutes.addBlock
  refine join_ok _ _ (many_ok _ _ fun _ => add_good p _ _ _ _ _) (join_ok _ _
    (many_ok _ _ fun _ => join_ok _ _ (add_good p _ _ _ _ _) (add_good p _ _ _ _ _))
    (join_ok _ _ (many_ok _ _ fun _ => hash_good p _) ?_))
  exact join_ok _ _ (row_good p (by decide) _ _) (join_ok _ _ (row_good p (by decide) _ _)
    (join_ok _ _ (row_good p (by decide) _ _) (join_ok _ _ (row_good p (by decide) _ _)
      (join_ok _ _ (row_good p (by decide) _ _) (row_good p (by decide) _ _)))))

private theorem net_good : good (Semantics.net E hp hm S X η T) (cap p) := by
  unfold Semantics.net Semantics.rowsAt Routes.networkAt
  refine join_ok _ _ (anchors_ok 1 _ (small p 1 (by decide))) (join_ok _ _ (all_ok _ fun i => atom_good E S i)
    (join_ok _ _ (all_ok _ fun _ => map_good p _ _ _ _ _ _ _) (join_ok _ _ ?_ (row_good p (by decide) _ _))))
  unfold Routes.foldRows ECFoldRoutes.foldBlock
  exact join_ok _ _ (row_good p (by decide) _ _) (join_ok _ _ (row_good p (by decide) _ _)
    (join_ok _ _ (row_good p (by decide) _ _) (all_ok _ fun _ => add_block_good p _ _ _ _ _ _ _ _ _ _)))

/-- Maximum local degree before subdivision; equality gates and copy-cycle bits obey the same cap. -/
theorem degree (v : Fin (w3_factorGraph (Semantics.layout E hp hm S X η T)).nV) :
    (w3_factorGraph (Semantics.layout E hp hm S X η T)).deg v ≤ cap p := by
  let N := Semantics.net E hp hm S X η T
  let K := (Semantics.shape p m).size+1
  let A := (AnchoredLayout.block N.core K).A
  let f := AnchoredLayout.signal N.core N.name
  have h : bounded A (cap p) := by
    intro g; induction g using Fin.addCases with
    | left i => exact (S8J.degree_left (AnchoredLayout.anchors K).gate N.core.A.gate i).le.trans
                  (anchors_ok K _ (small p 1 (by decide)) i)
    | right i => exact (S8J.degree_right (AnchoredLayout.anchors K).gate N.core.A.gate i).le.trans
                  (net_good E hp hm S X η i)
  induction v using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left g => exact (NamedWires.oldDegree f A.gate g).le.trans (h g)
    | right j => exact (NamedWires.eqDegree f A.gate j).le.trans (small p 2 (by decide))
  | right j => exact (CopyCycle.bitDegree A.gate (NamedWires.next f) j).le.trans (small p 3 (by decide))

private theorem packet_length {m b n : ℕ} (hb : 1 ≤ b) (hw : n ≤ 256*m*b) :
    scale m b + n ≤ 16000000*m*b := by
  have h : scale m b ≤ 4000000*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
  calc _ ≤ 4000000*m*(3*b)+256*m*b := Nat.add_le_add h hw
       _ = 12000256*m*b := by ring
       _ ≤ _ := by gcongr; decide

section Packet
variable (hm : 1 ≤ blockCount (bitLen p)) (S : ECSeed p (blockCount (bitLen p)))

/-- A correct instance builder and a correct subdivision-port evaluator realize the Tag 6 pair count. -/
theorem realizes_of_eval (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*(2*bitLen p+1))
    (make port : List Bool → List Bool)
    (build : make (ECPair.word E T S X η) = encodeBTNInstance
      (ECPair.word E T S X η) (w3_factorGraph (Semantics.layout E hp hm S X η T)).subdivision
      (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (ECPair.word E T S X η) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph (Semantics.layout E hp hm S X η T)).subdivisionTensor
        (w3_factorChecks _ (Semantics.tests E hp hm S X η T)) v a then 1 else 0]) :
    Realizes make port 16000000 (ECPair.word E T S X η) (bitLen p) (ECPair.value E T S X η) := by
  let b := bitLen p; let m := blockCount b; let s := scale m b; let w := ECPair.word E T S X η
  let L := Semantics.layout E hp hm S X η T; let t := Semantics.tests E hp hm S X η T
  have hm' : 1 ≤ m := hm
  have hs : b+2 ≤ s := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hm')
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  obtain ⟨he,hg⟩ : 2*L.ne < s ∧ L.ng ≤ s := sizes E hp hm S X η hη
  have hn : L.nb ≤ L.ne := by simpa using Fintype.card_le_of_injective L.rep (Function.RightInverse.injective L.rep_bit)
  have hv : L.ng+L.nb+L.ne ≤ 2*s := by omega
  have hw : w.length ≤ 256*m*b := ECPair.wordLen E S X η hm' hT hη
  have h1 : s+w.length ≤ 16000000*m*b := packet_length hb hw
  change Realizes make port _ _ _ (Semantics.ECPairCount E S X η T)
  rw [← Semantics.AcceptedEquiv E hp hm S X η hT]
  apply wireRealizes make port 16000000 s b w (w3_factorGraph L) (w3_factorChecks L t)
    (w3_factorEquiv L t) (by omega) (by omega) he
  · change L.ng+L.nb+L.ne ≤ s^16000000
    have hsq : 2*s ≤ s^2 := by rw [pow_two]; exact Nat.mul_le_mul_right s (by omega)
    exact hv.trans (hsq.trans (Nat.pow_le_pow_right (by omega : 0 < s) (by decide : 2 ≤ 16000000)))
  · apply (max_le (Finset.sup_le (fun v _ => degree E hp hm S X η v))
      ((by decide : 2 ≤ 12).trans (le_max_left _ _))).trans
    apply (S8G.FpMoment.degreeBudget hm').trans
    apply Nat.ceil_mono; apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast (show S8G.FpMoment.scale m b ≤ s by
      unfold S8G.FpMoment.scale s scale; gcongr; decide)
  · exact h1
  · apply h1.trans; rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
    exact ((Nat.mul_le_mul_right b (S8G.FpMoment.blockUpper b)).trans
      (by nlinarith : (b+2)*b ≤ (b+1)^2)).trans (Nat.pow_le_pow_right (by omega) (by decide))
  · exact build
  · intro v a; refine ⟨?_,eval v a⟩
    have hi : v.val < 2*s := v.isLt.trans_le hv
    have hd : ((w3_factorGraph L).subdivision.deg v) ≤ 2*L.ne :=
      (List.length_filter_le ..).trans (List.length_finRange.le.trans ((w3_factorGraph L).subdivision_nE.le))
    have hc := w3_queryIndexLength v.val; rw [w3_queryExactLength,List.length_ofFn]
    exact (by omega : _ ≤ 10*(s+w.length+1)).trans (Nat.mul_le_mul (by decide) (Nat.le_self_pow (by decide) _))

end Packet
end DetDLP.S8M.Bounds


