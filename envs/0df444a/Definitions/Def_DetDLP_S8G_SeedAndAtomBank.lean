-- Prove2me | Definitions.Def_DetDLP_S8G_SeedAndAtomBank
-- name    : DetDLP_S8G_SeedAndAtomBank
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:08:24.123985+00:00
-- url     : https://prove2.me/theorems/25bfc36d-250d-403e-a467-d4b140920572
-- title:
--   Declarative register seed bank and m-atom bank for Fp moments
-- statement:
--   **Seed bank.** For each $i<m$, the range rows check $a_{0,i}<p-1$ and $b_i<p$. The addition rows check $a_i=a_{0,i}+1$. The prefix rows compare $\eta$ with the encoding of $(a_0,b_0),\ldots,(a_{m-1},b_{m-1})$, reading each word from its most significant bit. A prefix longer than the encoding is rejected.
--
--   **Atom bank.** Slot $i$ uses the supplied coefficient words $a_i,b_i$. Its range rows check $x_i<p$, $z_i<p$, $z_i<T$, and the bound on the hash remainder. A low-to-high OR scan certifies $x_i\ne 0$. The two upper bounds on $z_i$ use the same value bits and separate witnesses. The arithmetic rows instantiate `HashRows.block` on $(a_i,x_i,b_i,z_i)$.
--
--   `seedBlock_iff` separates the slot checks from the prefix comparison. `atomBank_iff` reduces bank acceptance to acceptance at every index, including the empty-bank case. `orRows_iff` identifies the local scan with `w3_slotOr`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_FpAtomRows

set_option autoImplicit false
namespace DetDLP.S8G.SeedAndAtomBank
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.RangeRows S8H0.HashRows S8H0.GateRoutes S8H0.ResidueWires
variable {s : Shape} {d e : ℕ}

def allRows (m : ℕ) (f : Fin m → B (s.size+1)) : B (s.size+1) := match m, f with
  | 0, _ => rows 0 0 (fun i => i.elim0) (fun i => i.elim0)
  | n+1, g => many n g
theorem allRows_iff (m : ℕ) (f : Fin m → B (s.size+1)) (u : Bits (s.size+1)) :
    (allRows m f).OK u ↔ ∀ i, (f i).OK u := by cases m <;> simp [allRows, rows_iff, many_iff]

def seedSlot (d : ℕ) := Shape.pair (triple d) (.pair (triple d) (.pair (.word d) (.word (d+1))))
def seedShape (m d : ℕ) := Shape.vec m (seedSlot d)
def seedA (q : Path (seedSlot d) s) := word (n:=d) fun j => q (.snd (.snd (.fst j)))
def seedB (q : Path (seedSlot d) s) := word (n:=d) fun j => q (.snd (.fst (.fst j)))
def seedSlotBlock (p : ℕ) (q : Path (seedSlot d) s) :=
  joinB (checker (p-1) (fun j => q (.fst j))) (joinB (checker p (fun j => q (.snd (.fst j))))
    (sumRows (d+1) (word (n:=d) fun j => q (.fst (.fst j))) (pub 1) (seedA q)
      (fun i => .reg (q (.snd (.snd (.snd (.word i))))))))
def prefixBit {m : ℕ} (p : ℕ) (q : Path (seedShape m d) s) (j : ℕ) : Ref s :=
  if h : j < (m*2)*bitLen p then
    let t : Fin (m*2) × Fin (bitLen p) := finProdFinEquiv.symm ⟨j,h⟩
    let k : Fin m × Fin 2 := finProdFinEquiv.symm t.1
    let slot : Path (seedSlot d) s := fun a => q (.vec k.1 a)
    (if k.2 = 0 then seedA slot else seedB slot) t.2.rev.val
  else .pin false
def seedBlock (p m : ℕ) (η : List Bool) (path : Path (seedShape m d) s) :=
  joinB (allRows m fun i => seedSlotBlock p (fun a => path (.vec i a)))
    (rows η.length 1 (fun i _ => prefixBit p path i) (fun i f => decide (i.val < m*2*bitLen p ∧ f 0 = η[i])))
theorem seedBlock_iff (p m : ℕ) (η : List Bool) (q : Path (seedShape m d) s) (u : Bits (s.size+1)) :
    (seedBlock p m η q).OK u ↔ (∀ i, (seedSlotBlock p (fun a => q (.vec i a))).OK u) ∧
      ∀ i : Fin η.length, i.val < m*2*bitLen p ∧ (prefixBit p q i).eval u = η[i] := by
  simp only [seedBlock, joinB_iff, allRows_iff, rows_iff, decide_eq_true_eq]

/-- Local recurrence of `w3_slotOr`: each step consumes the next low bit; the last prefix must be true. -/
def orRows : (n : ℕ) → (Fin n → Ref s) → Ref s → (Fin n → Ref s) → B (s.size+1)
  | 0, _, b, _ => rows 1 1 (fun _ _ => b) (fun _ f => f 0)
  | n+1, x, b, t => joinB (rows 1 3 (fun _ => ![b,x 0,t 0])
      (fun _ f => decide (f 2 = (f 0 || f 1)))) (orRows n (x ∘ Fin.succ) (t 0) (t ∘ Fin.succ))

theorem orRows_iff (n : ℕ) (x t : Fin n → Ref s) (b : Ref s) (u : Bits (s.size+1)) (v : ℕ)
    (hx : ∀ i, (x i).eval u = v.testBit i.val) :
    (orRows n x b t).OK u ↔ w3_slotOr n v (b.eval u) (fun i => (t i).eval u) := by
  induction n generalizing b v with
  | zero => simp [orRows,rows_iff,w3_slotOr]
  | succ n ih =>
    have ht (i : Fin n) : ((x ∘ Fin.succ) i).eval u = (v/2).testBit i.val := by
      simpa only [Function.comp_apply,Fin.val_succ,Nat.testBit_succ] using hx i.succ
    rw [orRows,joinB_iff,ih _ _ _ _ ht,w3_slotOr]
    simp [rows_iff,hx,Nat.testBit_zero]

def atomSlot (d e : ℕ) := Shape.pair (triple d) (.pair (.word d) (.pair (.pair (.word d) (.word (d+1)))
  (.pair (run d e) (auxShape d))))
def atomBankShape (m d e : ℕ) := Shape.vec m (atomSlot d e)
def atomSlotBlock (hd : 1 ≤ d) (p T : ℕ) (a b : Word s) (q : Path (atomSlot d e) s) :=
  let r : Path (run d e) s := fun j => q (.snd (.snd (.snd (.fst j))))
  let h : Path (auxShape d) s := fun j => q (.snd (.snd (.snd (.snd j))))
  let l : Path (RegisterMap.mul d e) s := fun j => r (.snd (.fst (.snd (.snd (.fst j)))))
  let k : Path (RegisterMap.mul d e) s := fun j => r (.snd (.fst (.snd (.snd (.snd j)))))
  let x := word (n:=d) fun j => q (.fst (.fst j))
  let z := word (n:=d) fun j => r (.fst (.fst j))
  let w : Wires d hd s := {
    a := a, b := b, x := x, z := z, rem := word (n:=d) fun j => r (.snd (.fst (.fst (.fst j))))
    quot := word (n:=d) fun j => r (.snd (.fst (.snd (.fst j))))
    prod1 := word (n:=2*d) fun j => l (.fst j), prod2 := word (n:=2*d) fun j => k (.fst j)
    mul1 := fun i => (word (n:=e) fun j => l (.snd j)) i, mul2 := fun i => (word (n:=e) fun j => k (.snd j)) i
    sum := word (n:=d+1) fun j => h (.snd (.fst j)), cp := fun i => .masked (p.testBit i) (r (.snd (.snd .bit)))
    carry1 := fun i => .reg (h (.fst (.word i))), carry2 := fun i => .reg (h (.snd (.snd (.fst (.word i)))))
    carry3 := fun i => .reg (h (.snd (.snd (.snd (.word i))))) }
  let bound : Path (triple d) s := fun j => match j with
    | .fst v => r (.fst (.fst v)) | .snd c => q (.snd (.snd (.fst c)))
  joinB (checker p (fun j => q (.fst j))) (joinB (orRows d (fun i => x i) (.pin false)
    (fun i => .reg (q (.snd (.fst (.word i)))))) (joinB (checker p (fun j => r (.fst j)))
    (joinB (checker T bound) (joinB (checker p (fun j => r (.snd (.fst (.fst j))))) (HashRows.block p w)))))
def atomBankBlock (hd : 1 ≤ d) (p m T : ℕ) (aWords bWords : Fin m → Word s)
    (path : Path (atomBankShape m d e) s) : B (s.size+1) :=
  allRows m fun i => atomSlotBlock hd p T (aWords i) (bWords i) (fun j => path (.vec i j))
theorem atomBank_iff (hd : 1 ≤ d) (p m T : ℕ) (a b : Fin m → Word s)
    (q : Path (atomBankShape m d e) s) (u : Bits (s.size+1)) : (atomBankBlock hd p m T a b q).OK u ↔
      ∀ i, (atomSlotBlock hd p T (a i) (b i) (fun j => q (.vec i j))).OK u := allRows_iff ..

end DetDLP.S8G.SeedAndAtomBank


