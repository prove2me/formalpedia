-- Prove2me | Definitions.Def_FixpReciprocal_replaceSq
-- name    : FixpReciprocal_replaceSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:27.624012+00:00
-- url     : https://prove2.me/theorems/772ad689-1fea-467c-a345-faa419676098
-- title:
--   The replacement circuit $\mathcal C'$ of the proof of Theorem 4.2
-- statement:
--   Given a circuit $\mathcal C$ of $N$ gates over the functions of Lemma 3.4, the circuit $\mathcal C'$ is built as follows. A gate $x_i=1-x_j$ becomes the clipped affine gate $[\![-x_j+1]\!]$, and a gate $x_i=[\![x_j+x_k]\!]$ becomes $[\![x_j+x_k]\!]$. A gate $x_i=x_j^2$ is replaced by a fresh copy of the seven-gate circuit with input $x_j$, retaining $x_i$ as its output and introducing six fresh variables for its other gate outputs.
--
--   **Formalization Note** The first $N$ positions of $\mathcal C'$ are the original variables, in order. The fresh variables of successive squaring gates follow them, in order and disjoint. Restriction to the original coordinates reads the first $N$ coordinates of a vector.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_RGate
import Definitions.Def_FixpReciprocal_squareProblem
import Definitions.Def_FixpReciprocal_squareCircuit

namespace FixpReciprocal

/-- Rename the input indices of a gate. -/
def RGate.relabel (ρ : ℕ → ℕ) : RGate → RGate
  | .aff a b c j k => .aff a b c (ρ j) (ρ k)
  | .recip j => .recip (ρ j)

/-- Where the wires of a gadget copy go: its input is `j`; its wires `1, …, 6` are the fresh variables
`f, …, f + 5`. -/
def wireMap (j f : ℕ) : ℕ → ℕ
  | 0 => j
  | w + 1 => f + w

/-- The gates at the original positions, and the fresh gates; `f` is the next fresh position. -/
def replaceAux (τ : ℚ) : ℕ → List SqGate → List RGate × List RGate
  | _, [] => ([], [])
  | f, .compl j :: gs =>
    let r := replaceAux τ f gs
    (.aff (-1) 0 1 j j :: r.1, r.2)
  | f, .clipSum j k :: gs =>
    let r := replaceAux τ f gs
    (.aff 1 1 0 j k :: r.1, r.2)
  | f, .sq j :: gs =>
    let r := replaceAux τ (f + 6) gs
    ((gadgetOut τ).relabel (wireMap j f) :: r.1,
      (gadgetBody τ).map (RGate.relabel (wireMap j f)) ++ r.2)

/-- **The circuit `C′` of the proof of Theorem 4.2.** "The gates `x_i = 1 − x_j` and `x_i = ⟦x_j + x_k⟧` are already
clipped affine gates. Replace each gate `x_i = x_j²` by a fresh copy of the seven-gate circuit from Lemma 4.1,
retaining `x_i` as its output and introducing six fresh variables for its other gate outputs."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12.

**Formalization Note.** The first `N` positions are the original variables, in order; the fresh variables
of successive squaring gates follow them, in order and disjoint. -/
def replaceSq (τ : ℚ) (C : List SqGate) : List RGate :=
  (replaceAux τ C.length C).1 ++ (replaceAux τ C.length C).2

/-- The first `n` coordinates of a vector ("restriction to the original coordinates"). -/
noncomputable def restrict {m : ℕ} (n : ℕ) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun i => lookup y i.val

end FixpReciprocal


