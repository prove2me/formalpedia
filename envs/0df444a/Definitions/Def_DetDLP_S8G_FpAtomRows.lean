-- Prove2me | Definitions.Def_DetDLP_S8G_FpAtomRows
-- name    : DetDLP_S8G_FpAtomRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:46:52.427817+00:00
-- url     : https://prove2.me/theorems/8ea4b74b-37e8-44a6-83bc-961524015004
-- title:
--   Declarative register-wired Fp atom and stage blocks
-- statement:
--   ## Routed arithmetic rows
--
--   This module defines reusable declarative row blocks over arbitrary register shapes. `atomShape` pairs two range-checked triples and `atomBlock` applies the shared strict-bound checker to both routed triples. `stageShape` records a quotient, two M5 multiplier certificates, and full-width addition carries. `stageBlock` combines product checks for the two multiplier instances with a sum-row check for the modular relation. The module proves the corresponding local acceptance decompositions and exports a routed little-endian word evaluation lemma.
--
--   The atom and stage APIs are generic row combinators; they do not assert an end-to-end hash-wire construction or a decoded-slice unique-witness theorem.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateRoutes
import Definitions.Def_DetDLP_S8C_FpAtom
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace DetDLP.S8G.FpAtomRows
open DetDLP.S8H0.RegisterMap DetDLP.S8H0.NamedBlocks
open DetDLP.S8H0.ResidueWires DetDLP.S8H0.RangeRows
open DetDLP.S8H0.HashRows DetDLP.S8H0.GateRoutes

abbrev atomWidth (p : ℕ) := DetDLP.S8C.atomWidth p
theorem atomWidth_pos (p : ℕ) : 1 ≤ atomWidth p := Nat.succ_pos _

/-- Two independently checked residue triples, conveniently routed as a pair. -/
def atomShape (d : ℕ) : Shape := .pair (triple d) (triple d)

/-- Quotient, first and second M5 multiplier certificates, and the addition carries. -/
def stageShape (d e : ℕ) : Shape :=
  .pair (.word d) (.pair (Shape.pair (Shape.word (2*d)) (Shape.word e))
    (.pair (Shape.pair (Shape.word (2*d)) (Shape.word e)) (.word (2*d))))

/-- Strict-bound check on a routed triple; independent of the enclosing shape. -/
def atomBlock {d : ℕ} {s : Shape} (p : ℕ)
    (path : Path (atomShape d) s) : B (s.size+1) :=
  joinB (checker p (fun a => path (.fst a)))
    (checker p (fun a => path (.snd a)))

theorem atomBlock_iff {d : ℕ} {s : Shape} (p : ℕ)
    (path : Path (atomShape d) s) (u : Bits (s.size+1)) :
    (atomBlock p path).OK u ↔
      (checker p (fun a => path (.fst a))).OK u ∧
      (checker p (fun a => path (.snd a))).OK u := by
  exact joinB_iff _ _ _

/-- The two product certificates used by a modular-multiplication stage. -/
def stageProducts {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p : ℕ)
    (x y q prod1 prod2 : Word s)
    (mul1 mul2 : Fin (w3_fpMulLayout d hd).nb → Ref s) : B (s.size+1) :=
  joinB (product hd x y prod1 mul1)
    (product hd q (pub p) prod2 mul2)

/-- The full-width equation `prod2 + z = prod1`. -/
def stageSum {d : ℕ} {s : Shape} (prod2 z prod1 : Word s)
    (carry : Fin (2*d) → Ref s) : B (s.size+1) :=
  sumRows (2*d) prod2 z prod1 carry

/-- M5 products and their full-width addition, with all wires caller-routed. -/
def stageBlock {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p : ℕ)
    (x y q prod1 prod2 z : Word s)
    (mul1 mul2 : Fin (w3_fpMulLayout d hd).nb → Ref s)
    (carry : Fin (2*d) → Ref s) : B (s.size+1) :=
  joinB (stageProducts hd p x y q prod1 prod2 mul1 mul2)
    (stageSum prod2 z prod1 carry)

theorem stageBlock_iff {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p : ℕ)
    (x y q prod1 prod2 z : Word s)
    (mul1 mul2 : Fin (w3_fpMulLayout d hd).nb → Ref s)
    (carry : Fin (2*d) → Ref s) (u : Bits (s.size+1)) :
    (stageBlock hd p x y q prod1 prod2 z mul1 mul2 carry).OK u ↔
      (product hd x y prod1 mul1).OK u ∧
      (product hd q (pub p) prod2 mul2).OK u ∧
      (sumRows (2*d) prod2 z prod1 carry).OK u := by
  unfold stageBlock stageProducts stageSum
  rw [joinB_iff, joinB_iff]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₁,h₂,h₃⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨⟨h₁,h₂⟩,h₃⟩

/-- A routed word evaluates to its little-endian integer value. -/
theorem routedWord_eval {n : ℕ} {s : Shape} (a : Path (.word n) s)
    (u : Bits (s.size+1)) (w : Bits n)
    (h : ∀ i : Fin n,
      (a (.word i)).get (s.decode (u ∘ Fin.castSucc)) = w i) :
    evalWord (word a) u (value w).val := word_eval a u w h

end DetDLP.S8G.FpAtomRows


