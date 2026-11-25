-- Prove2me | Definitions.Def_DetDLP_W3_FpIncidence
-- name    : DetDLP_W3_FpIncidence
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:44:22.907211+00:00
-- url     : https://prove2.me/theorems/b2fc89a1-ac74-4457-8e07-f3fd2e347166
-- title:
--   Bipartite incidence graphs for local tests on shared bits
-- statement:
--   Let a finite collection of gates read Boolean variables through a finite incidence set. Join each gate to the copy vertex of every variable it reads, and impose equality on all copies at that vertex. Restriction to one representative per variable gives the bijection
--   $$
--   \{\text{satisfying edge assignments}\}\simeq\{\text{bit assignments passing every gate}\}.
--   $$
--   The degree of each vertex counts its incidences. When a chosen family of lookup gates has the required addresses and degrees, this construction gives a wire core with the specified decoding and size bounds.

import Definitions.Def_DetDLP_W4_M5WordNetwork
import Definitions.Def_DetDLP_W3_GatedWireWeights

set_option autoImplicit false
namespace DetDLP
open w4_M5Network

/-- Every incidence is an edge from its test to its bit's copy vertex. -/
structure w3_FactorLayout where
  ng : ℕ
  nb : ℕ
  ne : ℕ
  gate : Fin ne → Fin ng
  bit : Fin ne → Fin nb
  rep : Fin nb → Fin ne
  rep_bit : ∀ b, bit (rep b) = b

def w3_factorGraph (A : w3_FactorLayout) : WireGraph where
  nV := A.ng + A.nb
  nE := A.ne
  endpoints e := (Fin.castAdd A.nb (A.gate e), Fin.natAdd A.ng (A.bit e))
  loopless e h := by have := congrArg Fin.val h; simp only [Fin.val_castAdd,Fin.val_natAdd] at this; have := (A.gate e).isLt; omega

theorem w3_gateInc (A : w3_FactorLayout) (g : Fin A.ng) (e : Fin A.ne) (h : A.gate e = g) :
    e ∈ (w3_factorGraph A).ports (Fin.castAdd A.nb g) :=
  (WireGraph.mem_ports ..).2 (Or.inl (congrArg (Fin.castAdd A.nb) h))

theorem w3_bitInc (A : w3_FactorLayout) (b : Fin A.nb) (e : Fin A.ne) (h : A.bit e = b) :
    e ∈ (w3_factorGraph A).ports (Fin.natAdd A.ng b) :=
  (WireGraph.mem_ports ..).2 (Or.inr (congrArg (Fin.natAdd A.ng) h))

abbrev w3_factorTest (A : w3_FactorLayout) :=
  (g : Fin A.ng) → ({e : Fin A.ne // A.gate e = g} → Bool) → Bool

def w3_factorChecks (A : w3_FactorLayout) (test : w3_factorTest A) :
    (v : Fin (w3_factorGraph A).nV) → (Fin ((w3_factorGraph A).deg v) → Bool) → Bool :=
  Fin.addCases (fun g a => test g fun e => a ((w3_factorGraph A).portIndex _ _ (w3_gateInc A g e.1 e.2)))
    (fun b a => decide (∀ e : {i : Fin A.ne // A.bit i = b},
      a ((w3_factorGraph A).portIndex _ _ (w3_bitInc A b e.1 e.2)) =
        a ((w3_factorGraph A).portIndex _ _ (w3_bitInc A b (A.rep b) (A.rep_bit b)))))

theorem w3_factorGet (A : w3_FactorLayout) (v : Fin (A.ng + A.nb)) (e : Fin A.ne)
    (h : e ∈ (w3_factorGraph A).ports v) :
    ((w3_factorGraph A).ports v).get ((w3_factorGraph A).portIndex v e h) = e :=
  WireGraph.get_portIndex _ _ _ _

theorem w3_factorSatisfies (A : w3_FactorLayout) (test : w3_factorTest A) (x : Fin A.ne → Bool) :
    (w3_factorGraph A).Satisfies (w3_factorChecks A test) x ↔
    (∀ g, test g (fun e => x e.1) = true) ∧ ∀ e, x e = x (A.rep (A.bit e)) := by
  constructor
  · intro h
    constructor
    · intro g; simpa only [w3_factorChecks,Fin.addCases_left,w3_factorGet A] using h (Fin.castAdd A.nb g)
    · intro e
      have hh := h (Fin.natAdd A.ng (A.bit e))
      simp only [w3_factorChecks,Fin.addCases_right] at hh
      simpa only [w3_factorGet A] using (of_decide_eq_true hh) ⟨e,rfl⟩
  · rintro ⟨ht,hb⟩ v
    induction v using Fin.addCases with
    | left g => simpa only [w3_factorChecks,Fin.addCases_left,w3_factorGet A] using ht g
    | right b =>
      simp only [w3_factorChecks,Fin.addCases_right]
      apply decide_eq_true; intro e; simpa only [w3_factorGet A,e.property] using hb e.1

def w3_factorEquiv (A : w3_FactorLayout) (test : w3_factorTest A) :
    {x // (w3_factorGraph A).Satisfies (w3_factorChecks A test) x} ≃
      {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} where
  toFun x := ⟨fun i => x.1 (A.rep i),by
    obtain ⟨ht,hb⟩ := (w3_factorSatisfies A test _).1 x.2
    intro g; simpa only [← hb] using ht g⟩
  invFun b := ⟨fun e => b.1 (A.bit e),(w3_factorSatisfies A test _).2
    ⟨b.2,fun e => by simp [A.rep_bit]⟩⟩
  left_inv x := Subtype.ext (funext fun e => ((w3_factorSatisfies A test _).1 x.2).2 e |>.symm)
  right_inv b := Subtype.ext (funext fun i => congrArg b.1 (A.rep_bit i))

theorem w3_gateDegree (A : w3_FactorLayout) (g : Fin A.ng) :
    (w3_factorGraph A).deg (Fin.castAdd A.nb g) =
      ((List.finRange A.ne).filter fun e => decide (A.gate e = g)).length := by
  unfold WireGraph.deg WireGraph.ports; congr 1
  apply List.filter_congr; intro e _
  change decide (Fin.castAdd A.nb (A.gate e) = Fin.castAdd A.nb g ∨
    Fin.natAdd A.ng (A.bit e) = Fin.castAdd A.nb g) = _
  have hne : Fin.natAdd A.ng (A.bit e) ≠ Fin.castAdd A.nb g := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_natAdd,Fin.val_castAdd] at this; omega
  simp [hne]

theorem w3_bitDegree (A : w3_FactorLayout) (b : Fin A.nb) :
    (w3_factorGraph A).deg (Fin.natAdd A.ng b) =
      ((List.finRange A.ne).filter fun e => decide (A.bit e = b)).length := by
  unfold WireGraph.deg WireGraph.ports; congr 1
  apply List.filter_congr; intro e _
  change decide (Fin.castAdd A.nb (A.gate e) = Fin.natAdd A.ng b ∨
    Fin.natAdd A.ng (A.bit e) = Fin.natAdd A.ng b) = _
  have hne : Fin.castAdd A.nb (A.gate e) ≠ Fin.natAdd A.ng b := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_natAdd,Fin.val_castAdd] at this
    have := (A.gate e).isLt; omega
  simp [hne]

def w3_incSlot {q : w3_Query} (A : w3_FactorLayout) {n : ℕ}
    (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) :
    Fin (w3_factorGraph A).nV ≃ (w3_lookupSlot q ⊕ Fin (n+A.nb)) :=
  finSumFinEquiv.symm |>.trans (Equiv.sumCongr s (Equiv.refl _)) |>.trans
    (Equiv.sumAssoc _ _ _) |>.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)

noncomputable def w3_incLookups {q : w3_Query} (A : w3_FactorLayout) {n : ℕ}
    (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) : Finset (Fin (w3_factorGraph A).nV) :=
  Finset.univ.image fun t : w3_lookupSlot q => Fin.castAdd A.nb (s.symm (.inl t))

theorem w3_incLookupCount {q : w3_Query} (A : w3_FactorLayout) {n : ℕ}
    (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) : (w3_incLookups A s).card = 4*q.m := by
  have hi : Function.Injective (fun t : w3_lookupSlot q => Fin.castAdd A.nb (s.symm (.inl t))) :=
    (Fin.castAdd_injective ..).comp (s.symm.injective.comp Sum.inl_injective)
  calc _ = (Finset.univ : Finset (w3_lookupSlot q)).card := Finset.card_image_of_injective _ hi
       _ = _ := by simp [w3_lookupSlot]; omega

theorem w3_incOrientation {q : w3_Query} (A : w3_FactorLayout) {n : ℕ}
    (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) (e : Fin A.ne) :
    ((w3_factorGraph A).endpoints e).2 ∉ w3_incLookups A s := by
  intro h; obtain ⟨t,_,ht⟩ := Finset.mem_image.mp h
  have := congrArg Fin.val ht
  change (s.symm (.inl t)).val = A.ng + (A.bit e).val at this
  have := (s.symm (.inl t)).isLt; omega

noncomputable def w3_incCore {q : w3_Query} {C S n : ℕ} (A : w3_FactorLayout)
    (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) (test : w3_factorTest A)
    (decodeBits : {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃
      {t // w3_valid q t})
    (address : (v : Fin (w3_factorGraph A).nV) → (Fin ((w3_factorGraph A).deg v) → Bool) → ℕ)
    (hinj : ∀ i, Function.Injective (q.addr i))
    (haddr : ∀ a : {a // (w3_factorGraph A).Satisfies (w3_factorChecks A test) a},
      ∀ (i : Fin q.m) (j : Fin 2) (b : Bool),
      let t := (decodeBits (w3_factorEquiv A test a)).1
      let v := (w3_incSlot A s).symm (.inl (i,j,b))
      address v (w3_wireLocal _ v a.1) = q.addr i (if b then t.2 i j else t.1 i j))
    (hlookup : ∀ t : w3_lookupSlot q, (w3_factorGraph A).deg (Fin.castAdd A.nb (s.symm (.inl t))) = q.k)
    (he : 2*A.ne ≤ S)
    (hd : ∀ v ∉ w3_incLookups A s, (w3_factorGraph A).deg v ≤ C * Nat.ceil ((q.b:ℝ)^((3:ℝ)/4)))
    (heq : 2 ≤ C * Nat.ceil ((q.b:ℝ)^((3:ℝ)/4)))
    (hshape : 2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
      S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧
      1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m) : w3_WireCore q C where
  G := w3_factorGraph A
  L := w3_incLookups A s
  S := S
  desc := q.input
  T := w3_gateWeight (w3_incSlot A s) address (w3_factorChecks A test)
  checks := w3_factorChecks A test
  decode := (w3_factorEquiv A test).trans decodeBits
  live a := w3_gateWeight_live _ _ _ _ a.2 _ _ hinj (haddr a)
  dead a := w3_gateWeight_dead _ _ _ a
  lookup_count := w3_incLookupCount A s
  lookup_degrees := by rintro v hv; obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hv; exact hlookup t
  orientation := w3_incOrientation A s
  core_edges := he
  core_degrees := hd
  equality_degree := heq
  shape := hshape

end DetDLP


