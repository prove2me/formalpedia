-- Prove2me | Definitions.Def_DetDLP_S8G_Routes
-- name    : DetDLP_S8G_Routes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:18:20.844763+00:00
-- url     : https://prove2.me/theorems/67386721-ec06-4be2-ae8b-88712858b50c
-- title:
--   Tag 1 four-branch moment register routes
-- statement:
--   The public tag $j\in\{0,1,2,3\}$ selects **Mass**, **Single**, **Double**, or **EqualProd**. Each branch checks the same seed prefix; the number of atom banks is $\min(j,2)$. Only EqualProd allocates a shared range-checked residue $z$. For a tuple of length $m\ge 1$, its chain starts at $A_0$ and routes $m-1$ modular multiplications through checked intermediate residues. Both final stages write to $z$; when $m=1$, bitwise equality pins each initial word directly to $z$. The theorems `chainBlock_iff` and `network_iff` characterize acceptance in terms of the routed rows, without taking a seed or tuple as a public parameter.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_SeedAndAtomBank
import Definitions.Def_DetDLP_S8G_FpMomentCert

set_option autoImplicit false
namespace DetDLP.S8G.Routes
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.RangeRows S8H0.ResidueWires S8H0.GateRoutes
open S8H0.HashRows SeedAndAtomBank FpAtomRows
variable {s : Shape} {d e m n : ℕ}

/-- The last stage writes to the caller's output, so only internal residues need storage. -/
def chainShape (n d e : ℕ) : Shape := .pair (.vec n (stageShape d e)) (.vec (n-1) (triple d))
def internal (q : Path (chainShape n d e) s) (i : Fin (n-1)) : Path (triple d) s :=
  fun a => q (.snd (.vec i a))
def residueWord (r : Path (triple d) s) := word (n:=d) fun a => r (.fst a)
def stageAt (hd : 1 ≤ d) (p : ℕ) (x : Word s) (ys : Fin n → Word s) (zOut : Word s)
    (q : Path (chainShape n d e) s) (i : Fin n) :=
  let r : Path (stageShape d e) s := fun a => q (.fst (.vec i a))
  let prev := if h : i.val = 0 then x else residueWord (internal q ⟨i.val-1, by omega⟩)
  let next := if h : i.val < n-1 then residueWord (internal q ⟨i.val,h⟩) else zOut
  stageBlock hd p prev (ys i) (word (n:=d) fun a => r (.fst a))
    (word (n:=2*d) fun a => r (.snd (.fst (.fst a))))
    (word (n:=2*d) fun a => r (.snd (.snd (.fst (.fst a))))) next
    (fun k => (word (n:=e) fun a => r (.snd (.fst (.snd a)))) k)
    (fun k => (word (n:=e) fun a => r (.snd (.snd (.fst (.snd a))))) k)
    (fun k => .reg (r (.snd (.snd (.snd (.word k))))))
def chainBlock (hd : 1 ≤ d) (p : ℕ) (x : Word s) (ys : Fin n → Word s) (zOut : Word s)
    (q : Path (chainShape n d e) s) :=
  joinB (rows (if n = 0 then d else 0) 2 (fun i => ![x i,zOut i]) (fun _ f => decide (f 0 = f 1)))
    (joinB (allRows (n-1) fun i => checker p (internal q i)) (allRows n (stageAt hd p x ys zOut q)))
theorem chainBlock_iff (hd : 1 ≤ d) (p : ℕ) (x : Word s) (ys : Fin n → Word s) (zOut : Word s)
    (q : Path (chainShape n d e) s) (u : Bits (s.size+1)) : (chainBlock hd p x ys zOut q).OK u ↔
    (n = 0 → ∀ i : Fin d, (x i).eval u = (zOut i).eval u) ∧
    (∀ i, (checker p (internal q i)).OK u) ∧ ∀ i, (stageAt hd p x ys zOut q i).OK u := by
  cases n <;> simp [chainBlock,joinB_iff,rows_iff,allRows_iff]

/-- Zero, one, or two atom banks; only EqualProd allocates a shared output and chains. -/
def copies (j : Fin 4) := min j.val 2
def outputs (j : Fin 4) := if j = 3 then 1 else 0

/-- Each pair counts atom banks and shared product outputs, respectively. -/
theorem routeCounts :
    (copies 0, outputs 0) = (0, 0) ∧ (copies 1, outputs 1) = (1, 0) ∧
    (copies 2, outputs 2) = (2, 0) ∧ (copies 3, outputs 3) = (2, 1) := by
  decide

def productShape (j : Fin 4) (m d e : ℕ) : Shape :=
  .pair (triple d) (.vec (copies j) (chainShape (m-1) d e))
def bank (j : Fin 4) (m d e : ℕ) : Shape := .pair (seedShape m d)
  (.pair (.vec (copies j) (atomBankShape m d e)) (.vec (outputs j) (productShape j m d e)))
variable {j : Fin 4}
def seeds : Path (seedShape m d) (bank j m d e) := fun a => .fst a
def atoms (k : Fin (copies j)) : Path (atomBankShape m d e) (bank j m d e) :=
  fun a => .snd (.fst (.vec k a))
def result (t : Fin (outputs j)) : Path (triple d) (bank j m d e) :=
  fun a => .snd (.snd (.vec t (.fst a)))
def stages (t : Fin (outputs j)) (k : Fin (copies j)) : Path (chainShape (m-1) d e) (bank j m d e) :=
  fun a => .snd (.snd (.vec t (.snd (.vec k a))))
def coeffA (i : Fin m) : Word (bank j m d e) := seedA fun a => seeds (.vec i a)
def coeffB (i : Fin m) : Word (bank j m d e) := seedB fun a => seeds (.vec i a)
def atom (k : Fin (copies j)) (i : Fin m) : Word (bank j m d e) :=
  residueWord (d:=d) fun a => atoms k (.vec i (.fst a))
/-- For the empty tuple the initial accumulator is the empty product. -/
def initial (k : Fin (copies j)) : Word (bank j m d e) :=
  if h : 0 < m then atom k ⟨0,h⟩ else pub 1
def tail (k : Fin (copies j)) (i : Fin (m-1)) : Word (bank j m d e) := atom k ⟨i.val+1, by omega⟩
abbrev edges (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE

def network (hd : 1 ≤ d) (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) : B ((bank j m d (edges hd)).size+1) :=
  joinB (seedBlock p m η seeds) (joinB
    (allRows (copies j) fun k => atomBankBlock hd p m T coeffA coeffB (atoms k))
    (allRows (outputs j) fun t => joinB (checker p (result t))
      (allRows (copies j) fun k => chainBlock hd p (initial k) (tail k) (residueWord (result t)) (stages t k))))

/-- Every seed slot and prefix bit is checked, every allocated atom slot is checked, and
    the two EqualProd chains must finish at the very same range-checked residue. -/
theorem network_iff (hd : 1 ≤ d) (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool)
    (u : Bits ((bank j m d (edges hd)).size+1)) : (network hd p m j T η).OK u ↔
    ((∀ i, (seedSlotBlock p (fun a => seeds (.vec i a))).OK u) ∧
      ∀ i : Fin η.length, i.val < m*2*bitLen p ∧ (prefixBit p seeds i).eval u = η[i]) ∧
    (∀ k i, (atomSlotBlock hd p T (coeffA i) (coeffB i) (fun a => atoms k (.vec i a))).OK u) ∧
    ∀ t, (checker p (result t)).OK u ∧ ∀ k,
      (chainBlock hd p (initial k) (tail k) (residueWord (result t)) (stages t k)).OK u := by
  simp only [network,joinB_iff,allRows_iff,seedBlock_iff,atomBank_iff]

end DetDLP.S8G.Routes


