-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_CodeModel
-- name    : BinaryThreeLCC_Main_CodeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:16.262011+00:00
-- url     : https://prove2.me/theorems/c1885b49-b779-4930-ba0d-05a9f1bab59e
-- title:
--   Binary linear LCC and adaptive three-query oracle corrector
-- statement:
--   Let $\mathbb F_2$ be the two-element field. A code model consists of an injective linear map $C:\mathbb F_2^k\to\mathbb F_2^n$ and, for each requested position, an arbitrary probability mass function on all binary oracle decision trees of depth at most three. A branch can stop before depth three; queries may repeat and depend on earlier answers. Hamming distance counts differing coordinates. For parameters $\delta,\varepsilon$, operational local correction means
--
--   $$\Pr[\operatorname{Dec}^{y}(u)=C(b)_u]\ge1-\varepsilon
--   \quad\text{whenever }\Delta(y,C(b))\le\delta n.$$
--
--   The quantifiers range over every message, received word and requested position. Row vectors are computed by applying the encoding to coordinate basis vectors; padding appends exactly $n$ zero rows. No recovery equations or dimension bounds are bundled into the model.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Definition 1.1, printed p.1, PDF p.3; row construction in Fact 2.1, printed pp.2–3, PDF pp.4–5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Mathlib
import Definitions.Def_MantriCVQ_DT

set_option autoImplicit false

namespace BinaryThreeLCC.Main

abbrev Bit := ZMod 2

/-- The published oracle decision trees, restricted to the permitted query depth. -/
abbrev QueryTree (n d : ℕ) := {t : MantriCVQ.DT n // t.depth ≤ d}

/-- Identify the published Boolean input/output alphabet with ZMod 2. -/
def runTree {n d : ℕ} (t : QueryTree n d) (y : Fin n → Bit) : Bit :=
  if t.val.eval (fun i => y i == 1) then 1 else 0

noncomputable def hamming {n : ℕ} (x y : Fin n → Bit) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- An injective binary linear encoding and an arbitrary distribution over depth-three
adaptive oracle decision trees for each requested coordinate. -/
structure CodeModel (k n : ℕ) where
  encoding : (Fin k → Bit) →ₗ[Bit] (Fin n → Bit)
  injective : Function.Injective encoding
  decoder : Fin n → PMF (QueryTree n 3)

/-- PMF outer measure gives the exact mass of any event; its total mass is one. -/
noncomputable def successProbability {k n : ℕ} (C : CodeModel k n)
    (y : Fin n → Bit) (u : Fin n) (b : Bit) : ℝ :=
  ((C.decoder u).toOuterMeasure {t | runTree t y = b}).toReal

/-- Definition 1.1: every message, received word in the Hamming ball, and requested bit. -/
def Corrects {k n : ℕ} (C : CodeModel k n) (δ ε : ℝ) : Prop :=
  ∀ (b : Fin k → Bit) (y : Fin n → Bit) (u : Fin n),
    (hamming y (C.encoding b) : ℝ) ≤ δ * n →
      1 - ε ≤ successProbability C y u (C.encoding b u)

noncomputable def codeRow {k n : ℕ} (C : CodeModel k n) (u : Fin n) : Fin k → Bit :=
  fun j => C.encoding (Pi.single j 1) u

/-- The first n rows are the encoding rows; the last n are zero. -/
noncomputable def paddedRow {k n : ℕ} (C : CodeModel k n) (u : Fin (2 * n)) : Fin k → Bit :=
  if h : u.val < n then codeRow C ⟨u.val, h⟩ else 0

end BinaryThreeLCC.Main


