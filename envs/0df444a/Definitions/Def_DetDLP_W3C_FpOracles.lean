-- Prove2me | Definitions.Def_DetDLP_W3C_FpOracles
-- name    : DetDLP_W3C_FpOracles
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:01:07.48517+00:00
-- url     : https://prove2.me/theorems/85f3e05d-3eb4-42e5-bad4-958e64110c2c

import Theorems.Thm_DetDLP_w3_fp_small_driver
import Theorems.Thm_DetDLP_m89_s1_fp_plan_prepare
import Theorems.Thm_DetDLP_m89_s1_fp_plan_enumerate
import Theorems.Thm_DetDLP_m89_s1_fp_plan_decode

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.W3C.FpOracles
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev Port := (A : PrimitiveMachine) × Fin A.tapeCount
abbrev run (a : Port) := RunsWithin a.1 a.2
noncomputable abbrev m (p : ℕ) := blockCount (bitLen p)
abbrev Plan (p : ℕ) := Option (ℕ × FpSeed p (m p))
abbrev Blocks (p : ℕ) := Fin (m p) → List (ZMod p)ˣ
abbrev input {p : ℕ} [Fact p.Prime] (h a : (ZMod p)ˣ) := encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val

/-- Specifications of the fixed slots, indexed by the same digit as the controller. -/
structure Kit (en de : Port) where
  ports : Fin 9 → Port
  (scanC prepC enumC decC netC buildC contractC updateC : ℕ)
  scan : ∀ p [Fact p.Prime] (h a : (ZMod p)ˣ), orderOf h = p-1 → ¬w3_large p (p-1) →
    w3_scanOutput (p-1) (Additive.ofMul h) (Additive.ofMul a) (fun u =>
      run (ports 0) (input h a) (countWord u) (mainTimeBound scanC (bitLen p)) (mainSpaceBound scanC (bitLen p)))
  prep : ∀ p [Fact p.Prime], ∃ L : Plan p, m89_fp_plan_ok L ∧ run (ports 1) (countWord p)
    (Encoding.encodeList id [countWord p,m89_fp_plan_word L]) (mainSpaceBound prepC (bitLen p)) (polyBound prepC (bitLen p))
  enumerate : ∀ p [Fact p.Prime] (L : Plan p), m89_fp_plan_ok L → ∃ B : Blocks p,
    (∀ i, (B i).Nodup ∧ (B i).toFinset = m89_fp_plan_block L i) ∧ run (ports 2)
      (Encoding.encodeList id [countWord p,m89_fp_plan_word L]) (encodeFpFactorBlocks B)
      (mainSpaceBound enumC (bitLen p)) (mainSpaceBound enumC (bitLen p))
  decompose : ∀ p [Fact p.Prime] (L : Plan p), m89_fp_plan_ok L → ∀ x : (ZMod p)ˣ,
    (∃ A B : Fin (m p) → (ZMod p)ˣ, (∀ i, A i ∈ m89_fp_plan_block L i ∧ B i ∈ m89_fp_plan_block L i) ∧ (∏ i, A i*B i) = x) →
    ∃ A B : Fin (m p) → (ZMod p)ˣ, (∀ i, A i ∈ m89_fp_plan_block L i ∧ B i ∈ m89_fp_plan_block L i) ∧ (∏ i, A i*B i) = x ∧
      run (ports 3) (Encoding.encodeList id [encodeNatListBin [p,(x : ZMod p).val],m89_fp_plan_word L])
        (encodeFpDecomp A B) (mainSpaceBound decC (bitLen p)) (polyBound decC (bitLen p))
  enumRef : ports 4 = en
  decompRef : ports 5 = de
  probe : ∀ q, w3_fpQueries q → ∃ (n : w3_Net q netC) (w : List Bool),
    run (ports 6) q.input (w3_packet n) (polyBound buildC q.input.length) (polyBound buildC q.input.length) ∧
    EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T) ∧ run (ports 7) (w3_packet n) w
      (polyBound contractC (n.S+n.desc.length)*mainTimeBound contractC q.b) (polyBound contractC (n.S+n.desc.length))
  update : ∀ M N [NeZero M], 2 ≤ M → 1 ≤ N → ∀ (s : w3_Rep M N) (r : w3_Row M N),
    IsModularLatticeBasis M s.2 → (∃ z ∈ w3_coset s, w3_holds r z) →
    ∃ t, w3_update r s t ∧ (¬w3_holds r s.1 → 2*Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) ∧
      run (ports 8) (encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2 (fun i => (r.1 i).val) r.2.val)
        (encodeCosetRep (fun i => (t.1 i).val) t.2) (polyBound updateC (N+bitLen M)) (polyBound updateC (N+bitLen M))

theorem available (counts : DetDLP.M89S1.CountOracle) (en de : Port) (net : w3_terminalOps w3_fpQueries) (update : w3_hnfOps) : Nonempty (Kit en de) := by
  obtain ⟨S,s,kS,hS⟩ := w3_fp_small_driver
  obtain ⟨P,u,_,_,kP,hP⟩ := m89_s1_fp_plan_prepare counts
  obtain ⟨E,e,kE,hE⟩ := m89_s1_fp_plan_enumerate counts
  obtain ⟨D,d,kD,hD⟩ := m89_s1_fp_plan_decode counts
  obtain ⟨C,c,B,b,_,_,T,t,kT,_,_,hT⟩ := net
  obtain ⟨H,i,kH,hH⟩ := update
  let slots : Fin 9 → Port := ![⟨S,s⟩,⟨P,u⟩,⟨E,e⟩,⟨D,d⟩,en,de,⟨B,b⟩,⟨T,t⟩,⟨H,i⟩]
  refine ⟨⟨slots,kS,kP,kE,kD,C,c,kT,kH,hS,?_,hE,hD,rfl,rfl,?_,hH⟩⟩
  · intro p hp; obtain ⟨L,ok,r,_⟩ := hP p; exact ⟨L,ok,r⟩
  · intro q hq; obtain ⟨n,r,_,w,hw,rt⟩ := hT q hq; exact ⟨n,w,r,hw,rt⟩

end DetDLP.W3C.FpOracles


