-- Prove2me | Definitions.Def_DetDLP_S8H0_GraphDegree
-- name    : DetDLP_S8H0_GraphDegree
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:04:34.834172+00:00
-- url     : https://prove2.me/theorems/ecf3feae-40c0-4567-9fe3-a70dec854ec7
-- title:
--   Tag 0 anchored point-graph degree bound
-- statement:
--   **Degree bound.** Let $G_{p,c}$ be the factor graph of the Tag 0 anchored point layout with parameter $p$ and coefficients $c$. For every vertex $v$,
--   $$\deg_{G_{p,c}}(v)\leq\max\!\left\{12,\left\lceil136\bigl(\operatorname{bitLen}(p)+2\bigr)^{3/4}\right\rceil\right\}.$$
--   The multiplication incidence bound controls the product gates. The remaining row bounds are constant and are preserved under block joins. In the anchored copy cycle, each original gate retains its incidence count, each equality gate has degree $2$, and each bit vertex has degree $3$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GraphBudget

set_option autoImplicit false
namespace DetDLP.S8H0.GraphDegree
open PointGraph GateSemantics GateRoutes RegisterMap NamedBlocks RangeRows S8J S8H

def bounded (A : w3_FactorLayout) (k : ℕ) := ∀ i, degreeOf A.gate i ≤ k
def good {k : ℕ} (b : B k) (D : ℕ) := bounded b.core.A D

theorem join_ok {n D : ℕ} (b c : B n) (hb : good b D) (hc : good c D) : good (joinB b c) D := by
  intro i; induction i using Fin.addCases with
  | left i => simpa [joinB,join] using hb i
  | right i => simpa [joinB,join] using hc i

theorem many_ok {k D : ℕ} (n : ℕ) (f : Fin (n+1) → B k) (h : ∀ i, good (f i) D) : good (many n f) D := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact join_ok _ _ (h 0) (ih _ fun i => h i.succ)

private theorem fiberBound {n k : ℕ} (f : Fin n → Fin k) (i : Fin k) (m : ℕ) (g : Fin n → Fin m)
    (inj : ∀ a b, f a = i → f b = i → g a = g b → a = b) : degreeOf f i ≤ m := by
  let F := (List.finRange n).filter fun e => decide (f e = i)
  have nd : F.Nodup := (List.nodup_finRange n).filter _
  have h : Function.Injective (fun x : ↥F.toFinset => g x.val) := by
    intro a b he; apply Subtype.ext; apply inj _ _ (by simpa [F] using a.property) (by simpa [F] using b.property) he
  have hh := Fintype.card_le_of_injective _ h
  rw [Fintype.card_coe,List.toFinset_card_of_nodup nd,Fintype.card_fin] at hh; exact hh

theorem row_ok {s : Shape} (n m : ℕ) (r : Fin n → Fin m → Ref s) (test : Fin n → (Fin m → Bool) → Bool) : good (rows n m r test) m := by
  intro i; apply fiberBound _ i m (fun j => (finProdFinEquiv.symm j).2)
  intro a b ha hb he; apply finProdFinEquiv.symm.injective
  exact Prod.ext (ha.trans hb.symm) he

theorem add_ok {s : Shape} {n : ℕ} (cin : Bool) (a b z c : Fin n → Ref s) : good (NamedBlocks.add cin a b z c) 5 := by
  intro i; exact (w3_gateDegree (S8C.AddLayout.layout n) i).symm.le.trans (S8C.AddLayout.gateDegree i)

theorem anchors_ok (n D : ℕ) (hd : 1 ≤ D) : bounded (AnchoredLayout.anchors n) D := by
  intro i; apply (fiberBound _ i 1 (fun _ => 0) (fun _ _ h k _ => h.trans k.symm)).trans hd

theorem mono {k : ℕ} {b : B k} {l u : ℕ} (hl : good b l) (h : l ≤ u) : good b u := fun i => (hl i).trans h

noncomputable def cap (p : ℕ) := max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4)))
theorem small (p n : ℕ) (h : n ≤ 12) : n ≤ cap p := h.trans (le_max_left ..)

theorem mul_ok {s : Shape} (p : ℕ) (r : Fin (w3_fpMulLayout (d p) (hd p)).nb → Ref s) :
    good (mapped _ (w3_fpMulTests _ (hd p)) r) (cap p) := by
  change bounded (w3_fpMulLayout (d p) (hd p)) (cap p)
  intro i
  have H := (w3_fpMulIncidenceBounds (hd p)).2.2 i
  rw [w3_gateDegree] at H
  have hw : (d p : ℝ) + 1 = (bitLen p : ℝ) + 2 := by
    simp [d,ECPointArithmetic.width]; ring
  rw [hw] at H
  apply le_trans _ (le_max_right 12 _)
  exact_mod_cast H.le.trans (Nat.le_ceil _)

private theorem range_ok (p n e : ℕ) : good (RangeRows.block n e p) (cap p) := by
  unfold RangeRows.block
  refine join_ok _ _ (join_ok _ _ ?_ ?_) (many_ok _ _ fun _ => join_ok _ _ ?_ ?_)
  all_goals exact mono (add_ok _ _ _ _ _) (small p 5 (by decide))

private theorem hash_ok {s : Shape} (p : ℕ) (w : HashRows.Wires (d p) (hd p) s) :
    good (HashRows.block p w) (cap p) := by
  unfold HashRows.block HashRows.product
  refine join_ok _ _ (join_ok _ _ (join_ok _ _ (mul_ok p w.mul1) ?_) (join_ok _ _ (mul_ok p w.mul2) ?_))
    (join_ok _ _ ?_ (join_ok _ _ ?_ ?_))
  all_goals first | exact mono (row_ok _ 2 _ _) (small p 2 (by decide)) | exact mono (add_ok _ _ _ _ _) (small p 5 (by decide))

private theorem curve_ok (p n e : ℕ) : good (CurveRows.block n e) (cap p) :=
  mono (row_ok n 5 _ _) (small p 5 (by decide))

theorem net_ok (p : ℕ) (c : Coeff) : good (net p c) (cap p) := by
  unfold net network
  exact join_ok _ _ (anchors_ok 1 _ (small p 1 (by decide)))
    (join_ok _ _ (range_ok p _ _) (join_ok _ _ (many_ok _ _ fun _ => hash_ok p _) (curve_ok p _ _)))

private theorem cycle_ok {k D : ℕ} (A : w3_FactorLayout) (f : Fin A.ne → Fin k)
    (next : Equiv.Perm (Fin A.ne)) (hn : next = NamedWires.next f)
    (h : bounded A D) (h3 : 3 ≤ D) (v : Fin (w3_factorGraph (CopyCycle.layout A.gate next)).nV) :
    (w3_factorGraph (CopyCycle.layout A.gate next)).deg v ≤ D := by
  subst next
  induction v using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left g => exact (NamedWires.oldDegree f A.gate g).le.trans (h g)
    | right j => exact (NamedWires.eqDegree f A.gate j).le.trans (by omega)
  | right j => exact (CopyCycle.bitDegree A.gate (NamedWires.next f) j).le.trans h3

theorem degree (p : ℕ) (c : Coeff) (v : Fin (w3_factorGraph (layout p c)).nV) :
    (w3_factorGraph (layout p c)).deg v ≤ cap p := by
  let K := (S (d p) (e p)).size+1
  let b := (net p c).core; let f := (net p c).name
  let u := (AnchoredLayout.block b K).A
  have h : bounded u (cap p) := by
    intro i; induction i using Fin.addCases with
    | left i => simpa [u,AnchoredLayout.block,join] using anchors_ok K _ (small p 1 (by decide)) i
    | right i => simpa [u,AnchoredLayout.block,join,b] using net_ok p c i
  exact cycle_ok u (AnchoredLayout.signal b f) (W p c).next rfl h (small p 3 (by decide)) v

end DetDLP.S8H0.GraphDegree


