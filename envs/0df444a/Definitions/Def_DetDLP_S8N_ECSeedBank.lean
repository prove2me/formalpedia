-- Prove2me | Definitions.Def_DetDLP_S8N_ECSeedBank
-- name    : DetDLP_S8N_ECSeedBank
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:57:21.540554+00:00
-- url     : https://prove2.me/theorems/bb4f6714-d4d4-4201-9fc1-c76d33ea7232
-- title:
--   Tag 2 variable EC-seed register bank and SeedCert bijection
-- statement:
--   Defines a variable register bank for the two parity-class EC affine-seed pairs at each index. Each parity slot checks the canonical ranges and increment witness; the routed prefix checks the requested ecBits bits. The certified register data is bijective with the EC moment seed mass via canonical encodings of (a,b), and massEquiv identifies that mass with SeedCert.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_SeedSliceEquiv
import Definitions.Def_DetDLP_S8I_ECMomentCert

set_option autoImplicit false
namespace DetDLP.S8N.ECSeedBank
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.RangeRows S8H0.HashRows S8H0.GateRoutes
open S8H0.ResidueWires DetDLP.S8G.SeedAndAtomBank
open DetDLP.S8I.ECMomentCert
variable {p m : ℕ} {s : Shape} {d : ℕ}

def ecSeedShape (m d : ℕ) := Shape.vec m (Shape.pair (seedSlot d) (seedSlot d))

def ecSeedA (q : Path (seedSlot d) s) := seedA q
def ecSeedB (q : Path (seedSlot d) s) := seedB q

def ecSeedSlotBlock (p : ℕ) (q : Path (seedSlot d) s) := seedSlotBlock p q

def ecSeedBlock (p m : ℕ) (η : List Bool) (path : Path (ecSeedShape m d) s) : B (s.size+1) :=
  joinB (allRows m fun i => joinB
    (ecSeedSlotBlock p (fun a => path (.vec i (.fst a))))
    (ecSeedSlotBlock p (fun a => path (.vec i (.snd a)))))
    (rows η.length 1 (fun i _ =>
      if h : i.val < m*2*bitLen p then
        let t : Fin (m*2) × Fin (bitLen p) := finProdFinEquiv.symm ⟨i.val,h⟩
        let j : Fin m × Fin 2 := finProdFinEquiv.symm t.1
        let q := fun a => path (.vec j.1 (if j.2 = 0 then .fst a else .snd a))
        (if j.2 = 0 then ecSeedA q else ecSeedB q) t.2.rev.val
      else .pin false)
      (fun i f => decide (i.val < m*2*bitLen p ∧ f 0 = η[i])))

theorem ecSeedBlock_iff (p m : ℕ) (η : List Bool) (q : Path (ecSeedShape m d) s) (u : Bits (s.size+1)) :
    (ecSeedBlock p m η q).OK u ↔
      (∀ i : Fin m, (ecSeedSlotBlock p (fun a => q (.vec i (.fst a)))).OK u ∧
        (ecSeedSlotBlock p (fun a => q (.vec i (.snd a)))).OK u) ∧
      ∀ i : Fin η.length, i.val < m*2*bitLen p ∧
        (if h : i.val < m*2*bitLen p then
          let t : Fin (m*2) × Fin (bitLen p) := finProdFinEquiv.symm ⟨i.val,h⟩
          let j : Fin m × Fin 2 := finProdFinEquiv.symm t.1
          let r := fun a => q (.vec j.1 (if j.2 = 0 then .fst a else .snd a))
          (if j.2 = 0 then ecSeedA r else ecSeedB r) t.2.rev.val
        else .pin false).eval u = η[i] := by
  simp only [ecSeedBlock, joinB_iff, allRows_iff, rows_iff, decide_eq_true_eq, joinB_iff]

private abbrev D (p : ℕ) := S8C.atomWidth p
private theorem bound (p : ℕ) : p ≤ 2 ^ D p :=
  (Nat.le_pow_clog (by decide : 1 < 2) p).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
private noncomputable abbrev ea (p : ℕ) := finEquiv ((Nat.sub_le p 1).trans (bound p))
private noncomputable abbrev eb (p : ℕ) := finEquiv (bound p)
private abbrev Pair (p : ℕ) := Fin (p-1) × Fin p
private def result (p : ℕ) (a : Fin (p-1)) : Fin (2 ^ D p) := ⟨a.val+1, by have := a.isLt; have := bound p; omega⟩
private theorem wide {n : ℕ} (x : Fin (2^n)) : x.val < 2^(n+1) :=
  x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
private theorem carries (p : ℕ) (a : Fin (p-1)) :
    ∃! c, w3_addColumns (D p+1) a.val 1 (result p a).val false c :=
  w3_addColumns_unique (by have := wide (result p a); change a.val+1 < _ at this; omega)
    (Nat.one_lt_two_pow (Nat.succ_ne_zero _)) (wide (result p a)) rfl
private noncomputable def pack (p : ℕ) (x : Pair p) : (seedSlot (D p)).Data :=
  ((ea p).symm x.1 |>.val, ((eb p).symm x.2).val, (numBits _).symm (result p x.1), (carries p x.1).exists.choose)
private theorem pack_inj (p : ℕ) : Function.Injective (pack p) := by
  intro x y h; apply Prod.ext
  · apply (ea p).symm.injective; exact Subtype.ext (congrArg Prod.fst h)
  · apply (eb p).symm.injective; exact Subtype.ext (congrArg (fun z => z.2.1) h)

def ecSeedOK (p m : ℕ) (η : List Bool) (v : (ecSeedShape m (D p)).Data) : Prop :=
  ∃ S : DetDLP.S8I.ECQueryCount.Mass p m η, ∀ i, v i = (pack p (S.val i false), pack p (S.val i true))

noncomputable def ecSeedEquiv (p m : ℕ) [Fact p.Prime] (η : List Bool)
    (_hη : η.length ≤ m*4*bitLen p) :
    {v : (ecSeedShape m (D p)).Data // ecSeedOK p m η v} ≃ DetDLP.S8I.ECQueryCount.Mass p m η := by
  let f (S : DetDLP.S8I.ECQueryCount.Mass p m η) : {v // ecSeedOK p m η v} :=
    ⟨fun i => (pack p (S.val i false), pack p (S.val i true)), S, fun _ => rfl⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro S T h
    apply Subtype.ext
    funext i ε
    have hi := congrArg (fun z => z i) (congrArg Subtype.val h)
    cases ε
    · exact pack_inj p (congrArg Prod.fst hi)
    · exact pack_inj p (congrArg Prod.snd hi)
  · rintro ⟨v,S,h⟩
    exact ⟨S, Subtype.ext (funext fun i => (h i).symm)⟩

end DetDLP.S8N.ECSeedBank


