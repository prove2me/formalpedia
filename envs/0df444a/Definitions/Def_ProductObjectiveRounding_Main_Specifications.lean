-- Prove2me | Definitions.Def_ProductObjectiveRounding_Main_Specifications
-- name    : ProductObjectiveRounding_Main_Specifications
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:42.050549+00:00
-- url     : https://prove2.me/theorems/c9c4fdcd-06e5-4271-8af2-896015f4b84f
-- title:
--   Input serializations and uniform execution-based rounding guarantees
-- statement:
--   The main serialization lists counts, marginals, weights and unsorted row/variable/endpoint records. The internal fair-sign serialization additionally supplies ambient size, real accuracy or mass parameters, ordered incidence identifiers, boundaries and cross-pointers. Only these supplied data are initialized; no answer is present.
--
--   Define $L(n)=1+\log(2+n)$, $L_2(n)=1+\log(1+\log(2+n))$ and $H(n,B,\alpha)=1+\log(2+nB/\alpha)$. The main execution specification demands
--   $$F(x)\le e^\varepsilon W,\quad \mathrm{work}\le C_w\max(1,N)L_2(n),\quad \mathrm{depth}\le C_dL(n)^d.$$
--   The fair-sign version uses $\max(1,m)$ and the same doubly logarithmic overhead. The preliminary version uses $C_w\max(1,m)B^{12}\alpha^{-8}H^a$ work and $C_d(1+B/\alpha+L(n))^d$ depth. Each predicate expands to actual PRAM execution under every legal write arbitration, with polynomial word/address ranges. Uniform quantification of programs and constants is done explicitly in the theorem statements. Padding handles bounded sizes and changes no asymptotic regime.
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, Theorem 1.1, p.4; §2, pp.6–7; Theorem 4.1 and Lemma 4.2, p.13; Lemmas 4.3–4.4, pp.14,16; input representation, p.13

import Definitions.Def_ProductObjectiveRounding_Main_Input
import Definitions.Def_ProductObjectiveRounding_Main_FairInput
import Definitions.Def_ProductObjectiveRounding_Main_PRAM

open scoped BigOperators
noncomputable section

namespace ProductObjectiveRounding.Main

/-- Positive padding of logarithms changes no asymptotic regime, including n=0. -/
def L (n : ℕ) : ℝ := 1 + Real.log (2 + (n : ℝ))
def L₂ (n : ℕ) : ℝ := 1 + Real.log (1 + Real.log (2 + (n : ℝ)))
def logParameter (n : ℕ) (B α : ℝ) : ℝ :=
  1 + Real.log (2 + (n : ℝ) * B / α)

/-- Sparse unsorted input: counts, marginals, weights, then explicit incidence records.
Only the supplied input is present initially; sorting and all output writes are charged. -/
def ProductInput.encoding (I : ProductInput) : List PRAM.Cell :=
  [.word I.shape.u, .word I.shape.k, .word I.shape.m] ++
  (List.ofFn fun j => PRAM.Cell.num (I.marginal j)) ++
  (List.ofFn fun i => PRAM.Cell.num (I.weight i)) ++
  (List.ofFn fun e =>
    [PRAM.Cell.word (I.shape.row e).val, .word (I.shape.varIndex e).val,
      .num (I.endpoint e false), .num (I.endpoint e true)]).flatten

/-- Prepared fair-sign input includes ordered identifiers, segment boundaries and both
cross-pointers. These are input data in §4; the goal must construct them from unsorted data. -/
def FairInput.encoding (I : FairInput) (parameters : List ℝ) : List PRAM.Cell :=
  [.word I.shape.u, .word I.shape.k, .word I.shape.m, .word I.ambient] ++
  parameters.map PRAM.Cell.num ++
  (List.ofFn fun i => PRAM.Cell.num (I.weight i)) ++
  (List.ofFn fun e =>
    [PRAM.Cell.word (I.shape.row e).val, .word (I.shape.varIndex e).val,
      .num (I.coefficient e)]).flatten ++
  (List.ofFn fun e => PRAM.Cell.word (I.views.rowOrder e).val) ++
  (List.ofFn fun e => PRAM.Cell.word (I.views.variableOrder e).val) ++
  (List.ofFn fun i => PRAM.Cell.word (I.views.rowStart i)) ++
  (List.ofFn fun j => PRAM.Cell.word (I.views.variableStart j)) ++
  (List.ofFn fun e => PRAM.Cell.word (I.views.rowToVariable e).val) ++
  (List.ofFn fun e => PRAM.Cell.word (I.views.variableToRow e).val)

def ProductGuarantee (P : PRAM.Program) (Cw Cd : ℝ) (d r : ℕ)
    (ε : ℝ) (I : ProductInput) : Prop :=
  PRAM.Solves P I.shape.n r I.shape.u I.encoding
    (fun x => I.F x ≤ Real.exp ε * I.W)
    (Cw * (max 1 I.shape.size : ℕ) * L₂ I.shape.n)
    (Cd * L I.shape.n ^ d)

def FairGuarantee (P : PRAM.Program) (Cw Cd : ℝ) (d r : ℕ)
    (δ : ℝ) (parameters : List ℝ) (I : FairInput) : Prop :=
  PRAM.Solves P I.ambient r I.shape.u (I.encoding parameters)
    (fun x => I.F x ≤ Real.exp δ * I.W)
    (Cw * (max 1 I.shape.m : ℕ) * L₂ I.ambient)
    (Cd * L I.ambient ^ d)

/-- Absolute constants precede B, α and every instance; B and α are supplied real parameters. -/
def PreliminaryGuarantee (P : PRAM.Program) (Cw Cd : ℝ) (a d r : ℕ)
    (B α : ℝ) (I : FairInput) : Prop :=
  PRAM.Solves P I.ambient r I.shape.u (I.encoding [B, α])
    (fun x => I.F x ≤ Real.exp α * I.W)
    (Cw * (max 1 I.shape.m : ℕ) * B ^ 12 * (α⁻¹) ^ 8 *
      logParameter I.ambient B α ^ a)
    (Cd * (1 + B / α + L I.ambient) ^ d)

end ProductObjectiveRounding.Main


