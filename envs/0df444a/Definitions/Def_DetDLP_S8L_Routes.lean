-- Prove2me | Definitions.Def_DetDLP_S8L_Routes
-- name    : DetDLP_S8L_Routes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:09:27.385819+00:00
-- url     : https://prove2.me/theorems/502bd831-5a9d-449a-b8e1-8fa0c536c2d2
-- title:
--   Tag 5 register bank and declarative row network
-- statement:
--   Defines a public-parameter-indexed register-bank Shape for paired residue atoms, atom hash and threshold certificates, and intermediate modular-product stages. The network wires atom checks, product-stage checks, residue bounds, a pinned public output, and an interleaved tuple-word prefix into NamedBlocks. The public interface depends only on the stated parameters (including the public seed coefficients and prefix), and network_iff characterizes its acceptance as the conjunction of those named row-family acceptance conditions and prefix constraints.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_FpAtomRows
import Definitions.Def_DetDLP_S8L_FpPairChain

set_option autoImplicit false
namespace DetDLP.S8L.Routes
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.HashRows S8H0.ResidueWires
open S8H0.GateRoutes (Path word auxShape)
open S8H0.RangeRows (checker)
open S8G.FpAtomRows (stageShape stageBlock)

abbrev extra (d : ℕ) := Shape.pair (.word d) (.word d)
abbrev atom (d e : ℕ) := (triple d).pair ((extra d).pair ((triple d).pair ((run d e).pair (auxShape d))))
def bank (m d e : ℕ) : Shape := (.vec (2*m) (atom d e) : Shape).pair
  ((.vec (2*m-1) (stageShape d e) : Shape).pair (.vec (2*m-2) (triple d)))
variable {m d e : ℕ}
abbrev G (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE
abbrev A (i : Fin (2*m)) : Path (atom d e) (bank m d e) := fun j => .fst (.vec i j)
def elem (i : Fin (2*m)) : Word (bank m d e) := word (n:=d) fun j => A i (.fst (.fst j))
abbrev R (i : Fin (2*m)) : Path (run d e) (bank m d e) := fun j => A i (.snd (.snd (.snd (.fst j))))
abbrev H (i : Fin (2*m)) : Path (auxShape d) (bank m d e) := fun j => A i (.snd (.snd (.snd (.snd j))))
abbrev M₁ (i : Fin (2*m)) : Path (RegisterMap.mul d e) (bank m d e) := fun j => R i (.snd (.fst (.snd (.snd (.fst j)))))
abbrev M₂ (i : Fin (2*m)) : Path (RegisterMap.mul d e) (bank m d e) := fun j => R i (.snd (.fst (.snd (.snd (.snd j)))))
/-- The coefficients are the actual slope and intercept (the slope already includes the seed offset). -/
def hash (hd : 1 ≤ d) (p : ℕ) (c : ℕ × ℕ) (i : Fin (2*m)) : Wires d hd (bank m d (G hd)) where
  a := pub c.1; b := pub c.2; x := elem i
  z := word (n:=d) fun j => R i (.fst (.fst j))
  rem := word (n:=d) fun j => R i (.snd (.fst (.fst (.fst j))))
  quot := word (n:=d) fun j => R i (.snd (.fst (.snd (.fst j))))
  prod1 := word (n:=2*d) fun j => M₁ i (.fst j)
  prod2 := word (n:=2*d) fun j => M₂ i (.fst j)
  sum := word (n:=d+1) fun j => H i (.snd (.fst j))
  cp := fun j => .masked (p.testBit j) (R i (.snd (.snd .bit)))
  mul1 := fun j => .reg (M₁ i (.snd (.word j))); mul2 := fun j => .reg (M₂ i (.snd (.word j)))
  carry1 := fun j => .reg (H i (.fst (.word j)))
  carry2 := fun j => .reg (H i (.snd (.snd (.fst (.word j)))))
  carry3 := fun j => .reg (H i (.snd (.snd (.snd (.word j)))))

def atomRows (hd : 1 ≤ d) (p T : ℕ) (cs : Fin m → ℕ × ℕ) (i : Fin (2*m)) : B ((bank m d (G hd)).size+1) :=
  let c := cs ⟨i%m, Nat.mod_lt _ (by have := i.isLt; omega)⟩
  let w := hash hd p c i
  let t : Path (triple d) (bank m d (G hd)) := fun j => A i (.snd (.snd (.fst j)))
  let nz := add true (fun j : Fin d => .reg (A i (.snd (.fst (.fst (.word j)))))) (fun _ => .pin false)
    (fun j => elem i j) (fun j => .reg (A i (.snd (.fst (.snd (.word j))))))
  joinB (HashRows.block p w) (joinB (checker p fun j => A i (.fst j)) (joinB nz
    (joinB (checker p fun j => R i (.fst j)) (joinB (checker p fun j => R i (.snd (.fst (.fst j))))
      (joinB (checker (min T p) t) (eqs d (fun j => w.z j) fun j => .reg (t (.fst (.word j)))))))))

abbrev intermediate (i : Fin (2*m-2)) : Path (triple d) (bank m d e) := fun j => .snd (.snd (.vec i j))
def acc (i : Fin (2*m-2)) : Word (bank m d e) := word (n:=d) fun j => intermediate i (.fst j)
def stage (hd : 1 ≤ d) (p X : ℕ) (i : Fin (2*m-1)) : B ((bank m d (G hd)).size+1) :=
  let s : Path (stageShape d (G hd)) (bank m d (G hd)) := fun j => .snd (.fst (.vec i j))
  have hi := i.isLt
  let x := if h : i.val = 0 then elem ⟨0, by omega⟩ else acc ⟨i-1, by omega⟩
  let z := if h : i.val < 2*m-2 then acc ⟨i,h⟩ else pub X
  stageBlock hd p x (elem ⟨i+1, by omega⟩) (word (n:=d) fun j => s (.fst j))
    (word (n:=2*d) fun j => s (.snd (.fst (.fst j)))) (word (n:=2*d) fun j => s (.snd (.snd (.fst (.fst j))))) z
    (fun j => .reg (s (.snd (.fst (.snd (.word j)))))) (fun j => .reg (s (.snd (.snd (.fst (.snd (.word j)))))))
    (fun j => .reg (s (.snd (.snd (.snd (.word j))))))

/-- Factors are stored family-first, but prefix digits alternate the two words of each pair, MSB first. -/
def digit (p k : ℕ) : Ref (bank m d e) :=
  let b := bitLen p
  let pairIdx := k / b / 2
  if h : pairIdx < m then elem ⟨pairIdx + (if k / b % 2 = 0 then 0 else m), by split <;> omega⟩ (b-1-k%b)
  else .pin false

def prefixRows (p m d e X : ℕ) (η : List Bool) : B ((bank m d e).size+1) :=
  joinB (rows 1 0 (fun _ => Fin.elim0) fun _ _ => decide
    (η.length ≤ 2*m*bitLen p ∧ X < p ∧ X < 2^d ∧ (m = 0 → X = 1)))
    (rows η.length 1 (fun i _ => digit p i) fun i bits => bits 0 == η[i])

def allRows {k : ℕ} : (n : ℕ) → (Fin n → B (k+1)) → B (k+1)
  | 0, _ => eqs (s:=.word k) 0 Fin.elim0 Fin.elim0
  | n+1, f => joinB (f 0) (allRows n (fun i => f i.succ))
private theorem allRows_iff {k n : ℕ} (f : Fin n → B (k+1)) (u : Bits (k+1)) :
    (allRows n f).OK u ↔ ∀ i, (f i).OK u := by
  induction n with
  | zero =>
    apply Iff.intro
    · intro _ i; exact Fin.elim0 i
    · intro _; exact (eqs_iff (s:=.word k) 0 Fin.elim0 Fin.elim0 u).2 (by intro i; exact Fin.elim0 i)
  | succ n ih =>
    rw [allRows,joinB_iff,ih]
    constructor
    · intro h i
      rcases Fin.eq_zero_or_eq_succ i with hi | hi
      · simpa [hi] using h.1
      · rcases hi with ⟨j,rfl⟩; simpa using h.2 j
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩

def network (hd : 1 ≤ d) (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool) : B ((bank m d (G hd)).size+1) :=
  joinB (allRows _ (atomRows hd p T seedCoeffs)) (joinB (allRows _ (stage hd p X))
    (joinB (allRows _ fun i => checker p (intermediate i)) (prefixRows p m d (G hd) X η)))

theorem network_iff (hd : 1 ≤ d) (p m T X : ℕ) (seedCoeffs : Fin m → ℕ × ℕ) (η : List Bool)
    (u : Bits ((bank m d (G hd)).size+1)) : (network hd p m T X seedCoeffs η).OK u ↔
    (∀ i, (atomRows hd p T seedCoeffs i).OK u) ∧ (∀ i, (stage (m:=m) hd p X i).OK u) ∧
    (∀ i, (checker p (intermediate (d:=d) (e:=G hd) (m:=m) i)).OK u) ∧
    ((η.length ≤ 2*m*bitLen p ∧ X < p ∧ X < 2^d ∧ (m = 0 → X = 1)) ∧
    ∀ i : Fin η.length, (digit (m:=m) (d:=d) (e:=G hd) p i).eval u = η[i]) := by
  simp [network, joinB_iff, allRows_iff, prefixRows, rows_iff, and_assoc, imp_iff_not_or]

end DetDLP.S8L.Routes


