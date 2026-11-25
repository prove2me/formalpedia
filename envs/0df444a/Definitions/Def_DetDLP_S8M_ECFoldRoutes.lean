-- Prove2me | Definitions.Def_DetDLP_S8M_ECFoldRoutes
-- name    : DetDLP_S8M_ECFoldRoutes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:08:20.083964+00:00
-- url     : https://prove2.me/theorems/783739c0-5d9c-4b1f-ba4b-ea65f2b94179
-- title:
--   Declarative register chain routes for iterated short-Weierstrass addition
-- statement:
--   Defines a vector register shape containing one short-Weierstrass addition slice per stage. The fold block chains each stage output flag and coordinates into the next stage, applies the caller-supplied operand coordinates, and constrains the final flag and coordinates to a requested target. The zero-stage case pins the initial coordinates directly to the target. The characterization theorem states that the block is satisfied exactly when every addition slice is satisfied and all final coordinates agree bitwise with the target.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_ECAddRoutes
import Definitions.Def_DetDLP_S8G_Routes

set_option autoImplicit false
namespace DetDLP.S8M.ECFoldRoutes
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open DetDLP.S8N.ECAddRoutes
variable {s : Shape} {n d e : ℕ}

/-- One register-map slice for each short-Weierstrass addition. -/
def foldShape (n d e : ℕ) : Shape := .vec n (DetDLP.S8N.ECAddRoutes.addShape d e)

private abbrev slice (q : Path (foldShape n d e) s) (i : Fin n) :
    Path (DetDLP.S8N.ECAddRoutes.addShape d e) s := fun a => q (.vec i a)

private abbrev outFlag (q : Path (foldShape n d e) s) (i : Fin n) : Ref s :=
  .reg ((slice q i) (.fst (.fst .bit)))

private abbrev outX (q : Path (foldShape n d e) s) (i : Fin n) : Word s :=
  word (fun j : Addr (.word d) => (slice q i) (.fst (.snd (.vec 0 (.fst j)))))

private abbrev outY (q : Path (foldShape n d e) s) (i : Fin n) : Word s :=
  word (fun j : Addr (.word d) => (slice q i) (.fst (.snd (.vec 1 (.fst j)))))

private def foldStep (hd : 1 ≤ d) (p neg1 three c4Term : ℕ)
    (flag0 : Ref s) (x0 y0 : Word s) (flags : Fin n → Ref s)
    (xs ys : Fin n → Word s) (q : Path (foldShape n d e) s) (i : Fin n) :=
  let f := slice q i
  let prevFlag := if h : i.val = 0 then flag0 else outFlag q ⟨i.val - 1, by omega⟩
  let prevX := if h : i.val = 0 then x0 else outX q ⟨i.val - 1, by omega⟩
  let prevY := if h : i.val = 0 then y0 else outY q ⟨i.val - 1, by omega⟩
  DetDLP.S8N.ECAddRoutes.addBlock hd p neg1 three c4Term prevFlag prevX prevY (flags i) (xs i) (ys i) f

private def outputFlag (flag0 : Ref s) (q : Path (foldShape n d e) s) : Ref s :=
  if h : n = 0 then flag0 else outFlag q ⟨n - 1, by omega⟩

private def outputX (x0 : Word s) (q : Path (foldShape n d e) s) : Word s :=
  if h : n = 0 then x0 else outX q ⟨n - 1, by omega⟩

private def outputY (y0 : Word s) (q : Path (foldShape n d e) s) : Word s :=
  if h : n = 0 then y0 else outY q ⟨n - 1, by omega⟩

/-- Route n additions and pin the final flag and coordinates to the requested output. -/
def foldBlock (hd : 1 ≤ d) (p neg1 three c4Term : ℕ)
    (flag0 : Ref s) (x0 y0 : Word s) (flags : Fin n → Ref s)
    (xs ys : Fin n → Word s) (outFlag' : Ref s) (outX' outY' : Word s)
    (q : Path (foldShape n d e) s) : B (s.size+1) :=
  joinB (rows 1 2
    (fun _ => ![outputFlag flag0 q, outFlag']) (fun _ h => decide (h 0 = h 1))) <|
  joinB (rows d 2
    (fun i => ![(outputX x0 q) i, outX' i]) (fun _ h => decide (h 0 = h 1))) <|
  joinB (rows d 2
    (fun i => ![(outputY y0 q) i, outY' i]) (fun _ h => decide (h 0 = h 1)))
    (DetDLP.S8G.SeedAndAtomBank.allRows n (foldStep hd p neg1 three c4Term flag0 x0 y0 flags xs ys q))

theorem foldBlock_iff (hd : 1 ≤ d) (p neg1 three c4Term : ℕ)
    (flag0 : Ref s) (x0 y0 : Word s) (flags : Fin n → Ref s)
    (xs ys : Fin n → Word s) (outFlag' : Ref s) (outX' outY' : Word s)
    (q : Path (foldShape n d e) s) (u : Bits (s.size+1)) :
    (foldBlock hd p neg1 three c4Term flag0 x0 y0 flags xs ys outFlag' outX' outY' q).OK u ↔
    (∀ i, (foldStep hd p neg1 three c4Term flag0 x0 y0 flags xs ys q i).OK u) ∧
    (outputFlag flag0 q).eval u = outFlag'.eval u ∧
    (∀ i : Fin d, (outputX x0 q i).eval u = (outX' i).eval u) ∧
    (∀ i : Fin d, (outputY y0 q i).eval u = (outY' i).eval u) := by
  simp [foldBlock, joinB_iff, DetDLP.S8G.SeedAndAtomBank.allRows_iff, rows_iff,
    decide_eq_true_eq, and_assoc]
  <;> tauto

end DetDLP.S8M.ECFoldRoutes


