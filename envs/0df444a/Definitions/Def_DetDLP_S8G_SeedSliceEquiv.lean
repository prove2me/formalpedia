-- Prove2me | Definitions.Def_DetDLP_S8G_SeedSliceEquiv
-- name    : DetDLP_S8G_SeedSliceEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:21:52.09519+00:00
-- url     : https://prove2.me/theorems/d0e29067-d065-40fa-a057-d5a0bd4e4d1d
-- title:
--   Tag 1 seed register slice to Mass bijection
-- statement:
--   Establishes the exact bijection between accepted seed-register slices and prefix-filtered affine hash seeds Mass p m eta.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8G_AnchoredBank

set_option autoImplicit false
namespace DetDLP.S8G.SeedSliceEquiv
open S8H0 RegisterMap NamedBlocks RangeRows HashRows GateRoutes ResidueWires SeedAndAtomBank
variable {p m : ℕ}
private abbrev D := S8C.atomWidth
private theorem bound (p : ℕ) : p ≤ 2 ^ D p :=
  (Nat.le_pow_clog (by decide : 1 < 2) p).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
private noncomputable abbrev ea (p : ℕ) := finEquiv ((Nat.sub_le p 1).trans (bound p))
private noncomputable abbrev eb (p : ℕ) := finEquiv (bound p)
private abbrev Pair (p : ℕ) := Fin (p-1) × Fin p
private def result (a : Fin (p-1)) : Fin (2 ^ D p) := ⟨a.val+1, by have := a.isLt; have := bound p; omega⟩
private theorem wide {n : ℕ} (x : Fin (2^n)) : x.val < 2^(n+1) :=
  x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
private theorem carries (a : Fin (p-1)) : ∃! c, w3_addColumns (D p+1) a.val 1 (result a).val false c :=
  w3_addColumns_unique (by have := wide (result a); change a.val+1 < _ at this; omega)
    (Nat.one_lt_two_pow (Nat.succ_ne_zero _)) (wide (result a)) rfl
private noncomputable def pack (x : Pair p) : (seedSlot (D p)).Data :=
  ((ea p).symm x.1 |>.val, ((eb p).symm x.2).val, (numBits _).symm (result x.1), (carries x.1).exists.choose)
private theorem pack_inj : Function.Injective (@pack p) := by
  intro x y h; apply Prod.ext
  · apply (ea p).symm.injective; exact Subtype.ext (congrArg Prod.fst h)
  · apply (eb p).symm.injective; exact Subtype.ext (congrArg (fun z => z.2.1) h)
private theorem pack_a (x : Pair p) : (value (pack x).2.2.1).val = x.1.val+1 :=
  congrArg Fin.val ((numBits _).apply_symm_apply (result x.1))
private theorem pack_b (x : Pair p) : (value (pack x).2.1.1).val = x.2.val :=
  (finEquiv_val _ _).symm.trans (congrArg Fin.val ((eb p).apply_symm_apply x.2))

/-- A decoded slice consists of the canonical comparison and increment witnesses for a seed with prefix `η`. -/
def seedOK (p m : ℕ) (η : List Bool) (v : (seedShape m (D p)).Data) : Prop :=
  ∃ S : FpMoment.Mass p m η, ∀ i, v i = pack (S.val i)
noncomputable def seedEquiv (p m : ℕ) [Fact p.Prime] (η : List Bool) (_hη : η.length ≤ m*2*bitLen p) :
    {v // seedOK p m η v} ≃ FpMoment.Mass p m η := by
  let f (S : FpMoment.Mass p m η) : {v // seedOK p m η v} := ⟨fun i => pack (S.val i), S, fun _ => rfl⟩
  refine (Equiv.ofBijective f ⟨?_,?_⟩).symm
  · intro S T h; exact Subtype.ext (funext fun i => pack_inj (congrArg (fun v => v.val i) h))
  · rintro ⟨v,S,h⟩; exact ⟨S,Subtype.ext (funext fun i => (h i).symm)⟩
variable {s : Shape} {η : List Bool} (q : Path (seedShape m (D p)) s) (u : Bits (s.size+1))
variable (v : (seedShape m (D p)).Data) (hv : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v)
include hv
private theorem words (S : FpSeed p m) (h : ∀ i, v i = pack (S i)) (i : Fin m) :
    evalWord (seedA (fun j => q (.vec i j))) u ((S i).1.val+1) ∧
    evalWord (seedB (fun j => q (.vec i j))) u (S i).2.val := by
  rw [← pack_a (S i), ← pack_b (S i), ← h i]; exact
    ⟨word_eval _ _ _ (fun j => hv (.vec i (.snd (.snd (.fst (.word j)))))),
     word_eval _ _ _ (fun j => hv (.vec i (.snd (.fst (.fst (.word j))))))⟩

/-- Correctness in any containing register shape, without a hypothesis on unrelated bits. -/
theorem seedOK_iff (hη : η.length ≤ m*2*bitLen p) : (seedBlock p m η q).OK u ↔ seedOK p m η v := by
  have reg (j) : (Ref.reg (q j)).eval u = j.get v := ((Ref.reg (q j)).correct u).symm.trans (hv j)
  have slot (i : Fin m) : (seedSlotBlock p (fun a => q (.vec i a))).OK u ↔
      ∃ x : Pair p, v i = pack x := by
    rw [seedSlotBlock, joinB_iff, joinB_iff, checker_iff _ _ _ (v i).1 (fun j => reg (.vec i (.fst j))),
      checker_iff _ _ _ (v i).2.1 (fun j => reg (.vec i (.snd (.fst j)))), seedA,
      sum_spec (Nat.succ_pos (D p)) _ _ _ _ u
        (word_eval (fun j => q (.vec i (.fst (.fst j)))) u (v i).1.1 (fun j => hv (.vec i (.fst (.fst (.word j))))))
        (show evalWord (pub 1) u 1 from fun _ => rfl)
        (word_eval (fun j => q (.vec i (.snd (.snd (.fst j))))) u (v i).2.2.1
          (fun j => hv (.vec i (.snd (.snd (.fst (.word j)))))))]
    have hcarr : (fun j => (Ref.reg (q (.vec i (.snd (.snd (.snd (.word j))))))).eval u) = (v i).2.2.2 :=
      funext fun j => reg (.vec i (.snd (.snd (.snd (.word j)))))
    rw [hcarr]; change (below (p-1) (v i).1 ∧ below p (v i).2.1 ∧
      w3_addColumns _ (value (v i).1.1).val 1 (value (v i).2.2.1).val false (v i).2.2.2) ↔ _
    constructor
    · rintro ⟨ha,hb,hc⟩; let a := ea p ⟨(v i).1,ha⟩; let b := eb p ⟨(v i).2.1,hb⟩
      have hz := w3_addColumns_sound (wide _) (Nat.one_lt_two_pow (Nat.succ_ne_zero _)) (wide _) hc
      have he : value (v i).2.2.1 = result a := Fin.ext (by simpa [result,a,finEquiv_val] using hz.symm)
      refine ⟨(a,b), Prod.ext (congrArg Subtype.val ((ea p).symm_apply_apply ⟨(v i).1,ha⟩)).symm (Prod.ext
        (congrArg Subtype.val ((eb p).symm_apply_apply ⟨(v i).2.1,hb⟩)).symm (Prod.ext ?_ ?_))⟩
      · exact ((numBits _).symm_apply_eq.mpr he.symm).symm
      · apply (carries a).unique _ (carries a).exists.choose_spec; rw [← he]; exact hc
    · rintro ⟨⟨a,b⟩,h⟩; rw [h]; refine ⟨((ea p).symm a).property, ((eb p).symm b).property, ?_⟩
      rw [pack_a]; change w3_addColumns _ (value ((ea p).symm a).val.1).val 1 (result a).val false _
      have ha : (value ((ea p).symm a).val.1).val = a.val := (finEquiv_val _ _).symm.trans
        (congrArg Fin.val ((ea p).apply_symm_apply a))
      rw [ha]; exact (carries a).exists.choose_spec
  rw [seedBlock_iff]; simp only [slot]; constructor
  · rintro ⟨h,hp⟩; choose S hS using h; have w := words q u v hv S hS
    exact ⟨⟨S,(Semantics.prefix_iff q u S η hη (fun i => (w i).1) (fun i => (w i).2)).mp hp⟩, hS⟩
  · rintro ⟨S,h⟩; have w := words q u v hv S.val h
    exact ⟨fun i => ⟨_,h i⟩,(Semantics.prefix_iff q u S.val η hη (fun i => (w i).1) (fun i => (w i).2)).mpr S.property⟩

/-- The routed seed registers expose the shifted first and unshifted second coefficient. -/
theorem seedEquiv_words [Fact p.Prime] (hη : η.length ≤ m*2*bitLen p) (h : seedOK p m η v) (i : Fin m) :
    let S := (seedEquiv p m η hη ⟨v,h⟩).val
    evalWord (seedA (fun j => q (.vec i j))) u ((S i).1.val+1) ∧ evalWord (seedB (fun j => q (.vec i j))) u (S i).2.val := by
  apply words q u v hv; intro j
  exact (congrArg (fun z => z.val j) ((seedEquiv p m η hη).symm_apply_apply ⟨v,h⟩)).symm

end DetDLP.S8G.SeedSliceEquiv


