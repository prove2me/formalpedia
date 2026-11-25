-- Prove2me | Definitions.Def_DetDLP_D4NodeQuery
-- name    : DetDLP_D4NodeQuery
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:39:38.15671+00:00
-- url     : https://prove2.me/theorems/a9ae8230-3042-4863-ad13-7716f36017d8
-- title:
--   Balanced active-node branch requests
-- statement:
--   The active-node request carries the host map, graph, numerical parameters, modulus coefficients and rank. Preparing it calculates one balanced label and emits the specified Appendix D count or branch query. The contract also retains the terminal balance, soundness, local mode estimate and packet-entry oracle.

import Definitions.Def_DetDLP_D2_Greedy
set_option autoImplicit false
namespace DetDLP.D4NodeQuery
open AppendixD4 DetDLP_W1_Queries Polynomial OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
/-- A single adaptive node query, before computing the balanced label. -/
def request (G : Graph) {b : ℕ} (host : Fin b → Fin G.nV) (a u p l : ℕ) (f : ℤ[X]) (j : ℕ) := Encoding.encodeList id
  [D2.input G a host, encodeNatListBin [a,u,p,l], polynomialBits f, countWord j]
def emit (w rest : Bits) := true :: (frame w ++ rest)
def prepare (w : Bits) :=
  let data := first w
  let par := more w
  let inp := emit (first data) (emit (first par) (emit (first (more par)) (emit (D2.Greedy.run data) [false])))
  emit inp (emit (first (more (more par))) [false])
open OAI.Algorithms.SubexponentialSAT.Computation
noncomputable def Local : Prop := ∃ (M E : PrimitiveMachine) (o : Fin M.tapeCount) (oe : Fin E.tapeCount) (K H c : ℕ),
  ∀ (G : Graph) (a u p l b τ : ℕ) (host : Fin b → Fin G.nV) (f : ℤ[X]) (hf : f.Monic),
    1 ≤ u → (hu : u ≤ a) → u ≤ G.nE → 1 ≤ l → 1 ≤ p → RingOK f → points G.nE a ≤ 2^f.natDegree →
    2^a*64^(2*a) ≤ G.nE → (a+2)*64^(4*a)*max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
    (∀ z, (Finset.univ.filter fun y => host z=host y).card ≤ τ) →
    ∃ (lbl : Label a G) (s : Step lbl hu f l p) (order : Fin (Fintype.card (Branch s)) ≃ Branch s),
      let n := G.nE+p+f.natDegree+l+2
      let bound (j : ℕ) := polyBound H (request G host a u p l f j).length + polyBound K (n+(stepInput G a u p l f lbl).length) + c
      D2.Balanced host τ lbl ∧ Padded lbl ∧ s.sound hf ∧
      (∀ t, ((s.modes t).count:ℝ) ≤ Real.exp ((K:ℝ)*Real.sqrt ((G.nE:ℝ)*(p+increase G.nE a u (level t.val))/tileScale a (level t.val)))) ∧
      RunsWithin M o (request G host a u p l f 0) (countWord (Fintype.card (Branch s))) (bound 0) (bound 0) ∧
      (∀ j, RunsWithin M o (request G host a u p l f (j.val+1)) (s.bits hf (order j)) (bound (j.val+1)) (bound (j.val+1))) ∧
      ∀ t k β g r α, let z := s.child t k β g; RunsWithin E oe (Encoding.encodeList id [z.descriptor r,List.ofFn α]) (residue f l _ hf (z.entry r α)) (Real.exp ((K:ℝ)*(2^a:ℕ)*Real.log n)) (polyBound K n)
end DetDLP.D4NodeQuery


