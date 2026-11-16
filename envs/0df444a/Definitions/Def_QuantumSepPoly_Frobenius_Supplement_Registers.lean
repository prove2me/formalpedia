-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Registers
-- name    : QuantumSepPoly_Frobenius_Supplement_Registers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:47:24.084752+00:00
-- url     : https://prove2.me/theorems/87057613-7f4c-4422-b0a5-9c4a6cbee167
-- title:
--   Register basis and consistency/uniformity acceptance
-- statement:
--   One register is $[N]\times\Omega$ and a block contains $k$ registers. Explicit mixed-radix bijections flatten a block to dimension $(N|\Omega|)^k$ while preserving the two-party cut. The consistency projector checks repeated labels and every constrained pair. The uniformity projector sums the source tensor products over subsets with at least $\lceil k/(4|\Omega|)\rceil$ successful label projections.
--
--   Writing $\operatorname{Swap}_\ell$ for the exchange between matching registers in the two blocks, the acceptance operator is
--   $$M=\frac12\prod_{\ell=1}^k\frac{\mathrm{Id}+\operatorname{Swap}_\ell}{2}+\frac18\big((M_c+M_u)\otimes\mathrm{Id}+\mathrm{Id}\otimes(M_c+M_u)\big).$$
--   No operator bound, separability property, support estimate or multiplicativity is assumed by these constructions.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 28, 32–35 (PDF p. 28, 32–35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_SparseCSP
import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates

noncomputable section
open scoped BigOperators

namespace QuantumSepPoly.Frobenius.Supplement
abbrev Register (N A : ℕ) := Fin N × Fin A
abbrev Block (N A k : ℕ) := Fin k → Register N A
abbrev BlockOp (N A k : ℕ) := Matrix (Block N A k) (Block N A k) ℂ
abbrev TwoBlockOp (N A k : ℕ) :=
  Matrix (Block N A k × Block N A k) (Block N A k × Block N A k) ℂ

/-- Mixed-radix enumeration by recursively adjoining the last register. -/
def tupleEquiv (B k : ℕ) : (Fin k → Fin B) ≃ Fin (B^k) := finFunctionFinEquiv

def blockEquiv (N A k : ℕ) : Block N A k ≃ Fin ((N*A)^k) :=
  (Equiv.piCongrRight (fun _ => finProdFinEquiv)).trans (tupleEquiv (N*A) k)

def flatten {N A k : ℕ} (M : TwoBlockOp N A k) : Bip ((N*A)^k) :=
  fun i j => M ((blockEquiv N A k).symm i.1, (blockEquiv N A k).symm i.2)
    ((blockEquiv N A k).symm j.1, (blockEquiv N A k).symm j.2)

def consistency {N A : ℕ} (I : MaxCSP N 2 (Fin A)) (k : ℕ) : BlockOp N A k := by
  classical
  exact fun x y => if x = y then
    ((∏ l : Fin k, ∏ r : Fin k,
      (if (x l).1 = (x r).1 then (if (x l).2 = (x r).2 then 1 else 0) else 1) *
      edgePredicate I (x l).1 (x r).1 (x l).2 (x r).2 : ℝ) : ℂ) else 0

def uniformity (N A k : ℕ) : BlockOp N A k := by
  classical
  exact fun x y => ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter
      (fun S => Nat.ceil ((k : ℝ)/(4*A)) ≤ S.card),
    ∏ l : Fin k, if l ∈ S then (1 / ((N : ℂ)*A)) else
      (if (x l).1 = (y l).1 then
        (if (x l).2 = (y l).2 then 1 else 0) - 1/(A : ℂ) else 0)

def swapMatrix (N A k : ℕ) (l : Fin k) : TwoBlockOp N A k := by
  classical
  exact fun x y => if
    (Function.update y.1 l (y.2 l), Function.update y.2 l (y.1 l)) = x then 1 else 0

def acceptance {N A : ℕ} (I : MaxCSP N 2 (Fin A)) (k : ℕ) : TwoBlockOp N A k := by
  classical
  let C := consistency I k + uniformity N A k
  let swaps := (List.ofFn (fun l : Fin k => (1/2 : ℂ) • (1 + swapMatrix N A k l))).prod
  exact (1/2 : ℂ) • swaps + (1/8 : ℂ) • (fun x y =>
    C x.1 y.1 * (if x.2 = y.2 then 1 else 0) +
    (if x.1 = y.1 then 1 else 0) * C x.2 y.2)

def registerProduct {N A k : ℕ} (x : Fin k → Register N A → ℂ) : Block N A k → ℂ :=
  fun z => ∏ l, x l (z l)

def quadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, star (x i) * M i j * x j).re
end QuantumSepPoly.Frobenius.Supplement


