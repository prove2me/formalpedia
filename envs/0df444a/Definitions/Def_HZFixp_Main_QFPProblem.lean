-- Prove2me | Definitions.Def_HZFixp_Main_QFPProblem
-- name    : HZFixp_Main_QFPProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:51:13.483667+00:00
-- url     : https://prove2.me/theorems/00243c8b-fa38-47da-a7d5-475d6a9dead3
-- title:
--   Definition 3.1 — Quadratic Fixed Point
-- statement:
--   An instance of **Quadratic Fixed Point** is a map $F : [0,1]^d \to [0,1]^d$ each of whose coordinates $F_i$ is given as a list of monomials of degree at most two, $c \cdot \prod_{v \in S} x_v$ with $|S| \le 2$ (repetition allowed), whose rational coefficients $c$ satisfy $|c| \le 1$ and are written in binary. That $F$ maps the cube $[0,1]^d$ into itself is part of being an instance. A solution is a fixed point
--   $$x \in [0,1]^d,\qquad x = F(x).$$
--
--   Theorem 3.2 shows this problem is FIXP-hard; it is the first stage of the reduction from three-player Nash equilibrium to HZ equilibrium.
--
--   **Formalization Note.** A monomial is a pair (coefficient, list of $0$-based variable indices, of length at most two); the encoding writes $d$ and then the lists, all numbers in binary.
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 6 (PDF 8), Definition 3.1

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace HZFixp.Main

open OnlineCRS.Combine FixpReciprocal

/-- The data of a Quadratic Fixed Point instance: the dimension `d` and, for each coordinate of
`F`, its list of monomials; a monomial is a coefficient and the list of the (`0`-based) indices of
its variables, with repetition (`[]` a constant, `[v]` the variable `x_v`, `[v, w]` the product
`x_v x_w`). -/
structure QFPData where
  /-- the dimension -/
  d : ℕ
  /-- the monomial lists of the coordinates `F_1, …, F_d` -/
  coords : List (List (ℚ × List ℕ))

/-- The value `F_i(x)` of coordinate `i` at `x`: the sum of its monomials. -/
noncomputable def QFPData.evalF (D : QFPData) (x : Fin D.d → ℝ) (i : Fin D.d) : ℝ :=
  ((D.coords.getD i.val []).map
    (fun mono => (mono.1 : ℝ) * (mono.2.map (fun v => lookup x v)).prod)).sum

/-- **An instance of Quadratic Fixed Point (Definition 3.1):** "A map `F : [0, 1]^d → [0, 1]^d`,
where each coordinate is specified as a list of monomials of degree at most two, with rational
coefficients … of absolute value at most one." That `F` maps the cube into itself is part of
being an instance. -/
def QFPData.IsInstance (D : QFPData) : Prop :=
  D.coords.length = D.d ∧
  (∀ c ∈ D.coords, ∀ mono ∈ c, |mono.1| ≤ 1 ∧ mono.2.length ≤ 2 ∧ ∀ v ∈ mono.2, v < D.d) ∧
  ∀ x : Fin D.d → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → ∀ i, D.evalF x i ∈ Set.Icc (0 : ℝ) 1

/-- Instances of Quadratic Fixed Point. -/
def QFPInst : Type := {D : QFPData // D.IsInstance}

/-- Binary encoding of a monomial: its coefficient, then its list of variable indices. -/
def encMono (mono : ℚ × List ℕ) : List Sym := fRat mono.1 ++ fList fNat mono.2

theorem encMono_prefixFree : PrefixFree encMono := by
  intro a b s t h
  simp only [encMono, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fRat_prefixFree h
  obtain ⟨h2, h⟩ := fNat_prefixFree.fList h
  exact ⟨Prod.ext h1 h2, h⟩

/-- Binary encoding of an instance ("rational coefficients encoded in binary"). -/
def encQFPData (D : QFPData) : List Sym := fNat D.d ++ fList (fList encMono) D.coords

theorem encQFPData_injective : Function.Injective encQFPData := by
  rintro ⟨d, c⟩ ⟨d', c'⟩ h
  simp only [encQFPData] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  have h2 := encMono_prefixFree.fList.fList.injective h
  simp_all

/-- **Quadratic Fixed Point as a search problem (Definition 3.1).** Output: "A vector
`x ∈ [0, 1]^d` satisfying `x = F(x)`."

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 6, Definition 3.1. -/
noncomputable def qfpProblem : RealSearch where
  Inst := QFPInst
  enc := fun I => encQFPData I.1
  enc_injective := fun _ _ h => Subtype.ext (encQFPData_injective h)
  dim := fun I => I.1.d
  Sol := fun I => {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ I.1.evalF x = x}

end HZFixp.Main


