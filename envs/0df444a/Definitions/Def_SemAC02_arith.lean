-- Prove2me | Definitions.Def_SemAC02_arith
-- name    : SemAC02_arith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:04.865466+00:00
-- url     : https://prove2.me/theorems/489b8ad3-b92a-41aa-ba52-28e9383a045e
-- title:
--   Arithmetisation $[\![A]\!]$ of an AC0[2] circuit
-- statement:
--   The **arithmetisation** of an AC0[2] circuit $A$ is the element $[\![A]\!]\in\mathcal B_n$ with $A(x)=1$ exactly when $[\![A]\!](x)=0$. It is defined by
--   $$
--   [\![0]\!]=1,\quad [\![1]\!]=0,\quad [\![x_i]\!]=1+x_i,\quad [\![\neg x_i]\!]=x_i,
--   $$
--   $$
--   \Bigl[\!\!\Bigl[\bigvee_i A_i\Bigr]\!\!\Bigr]=\prod_i[\![A_i]\!],\qquad
--   \Bigl[\!\!\Bigl[\bigwedge_i A_i\Bigr]\!\!\Bigr]=1+\prod_i\bigl(1+[\![A_i]\!]\bigr),\qquad
--   \Bigl[\!\!\Bigl[\bigoplus_i A_i\Bigr]\!\!\Bigr]=1+\sum_i\bigl(1+[\![A_i]\!]\bigr),
--   $$
--   with all operations in $\mathcal B_n$, empty products $1$ and empty sums $0$. It extends the clause polynomial $[\![C]\!]$ of a clause.
--
--   **Formalization Note** `arithRaw` is the formal polynomial given by the rules; `arith A` is its multilinear representative `AC02Frege.ML (arithRaw A)`.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble

namespace SemAC02

open MvPolynomial

/-- The formal arithmetisation of a circuit before multilinearisation (p.18): `⟦0⟧ = 1`,
`⟦1⟧ = 0`, `⟦x_i⟧ = 1 + x_i`, `⟦¬x_i⟧ = x_i`, `⟦⋁ A_i⟧ = ∏ ⟦A_i⟧`,
`⟦⋀ A_i⟧ = 1 + ∏ (1 + ⟦A_i⟧)`, `⟦⨁ A_i⟧ = 1 + ∑ (1 + ⟦A_i⟧)`, with empty products `1` and empty
sums `0`. -/
noncomputable def arithRaw {V : Type} : Circ V → MvPolynomial V (ZMod 2)
  | .const b => if b then 0 else 1
  | .lit v b => if b then 1 + X v else X v
  | .and cs => 1 + (cs.map (fun c => 1 + arithRaw c)).prod
  | .or cs => (cs.map (fun c => arithRaw c)).prod
  | .xor cs => 1 + (cs.map (fun c => 1 + arithRaw c)).sum

/-- The **arithmetisation** `⟦A⟧ ∈ B_n` of an AC0[2] circuit `A` (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §2.2, p.18): the polynomial with `A(x) = 1` exactly when `⟦A⟧(x) = 0`. "All
operations are in `B_n`."

**Formalization Note** Elements of `B_n = 𝔽₂[x]/⟨x_i² − x_i⟩` are represented by their unique
multilinear representatives; `⟦A⟧` is the multilinearisation `AC02Frege.ML` of the formal
arithmetisation `arithRaw A`. -/
noncomputable def arith {V : Type} (A : Circ V) : MvPolynomial V (ZMod 2) :=
  AC02Frege.ML (arithRaw A)

end SemAC02


