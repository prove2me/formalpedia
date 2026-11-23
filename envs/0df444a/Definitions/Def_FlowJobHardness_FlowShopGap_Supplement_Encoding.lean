-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Encoding
-- name    : FlowJobHardness_FlowShopGap_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:25:39.553969+00:00
-- url     : https://prove2.me/theorems/31d6792e-459b-4744-b40f-9481ec206cca
-- title:
--   Binary rational inputs and schedule outputs over the published shop model
-- statement:
--   A rational shop is the published finite real-duration job-shop instance together with rational durations equal to its processing times. Machine assignments, operation chains and all nonpreemptive feasibility constraints are inherited unchanged. Durations may be zero, chains may be empty or arbitrarily long, and general jobs may revisit machines.
--
--   The binary input writes the machine and job counts, then each chain length and its machine-duration pairs. A natural number $k$ is encoded by the unary length of its ordinary binary digit string, a zero separator, and those digits. A reduced rational is encoded by its sign, numerator magnitude and positive denominator. Hence
--   $$|\operatorname{code}(k)|=2|\operatorname{bits}(k)|+1.$$
--   All scheduling integers use logarithmic space in their magnitude; this is not unary processing-time input. The lists and their counts make the code uniquely readable.
--
--   Nonpreemptive outputs give rational operation start times. Preemptive outputs give rational window endpoints and a finite list of rational interval endpoints per operation. An optimization promise additionally encodes a positive rational objective threshold. Time complexity is measured by the total input bit length.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, pp. 20:1–20:2, §1 and footnote 1; pp. 20:5–20:7, Theorems 1.2–1.6

import Mathlib
import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Preemption
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

open JobShopLTAS.Core

/-- A finite binary-input refinement of the published real-duration shop.
The rational witness changes no chain or machine constraint. Zero durations,
empty chains and arbitrary repeated visits are allowed. -/
structure RationalShop where
  m : ℕ
  n : ℕ
  data : Instance m n
  duration : (j : Fin n) → Fin (data.μ j) → ℚ
  duration_eq : ∀ j i, (duration j i : ℝ) = data.p j i

/-- Self-delimiting binary natural: unary bit-length, a zero, then the bits
least-significant first. This uses O(log(k+2)) bits, not unary processing times. -/
def natCode (k : ℕ) : List Bool :=
  List.replicate (Nat.bits k).length true ++ false :: Nat.bits k

def ratCode (q : ℚ) : List Bool :=
  (decide (q < 0)) :: (natCode q.num.natAbs ++ natCode q.den)

/-- m,n; then for each job its chain length, and machine/duration pairs in order.
All counts and reduced numerator/denominator components are self-delimiting. -/
def shopCode (S : RationalShop) : List Bool :=
  natCode S.m ++ natCode S.n ++
    (List.ofFn fun j : Fin S.n => natCode (S.data.μ j) ++
      (List.ofFn fun i : Fin (S.data.μ j) =>
        natCode (S.data.π j i).val ++ ratCode (S.duration j i)).flatten).flatten

/-- Rational nonpreemptive start times, in job/operation order. -/
def startCode (S : RationalShop) (s : S.data.Op → ℚ) : List Bool :=
  (List.ofFn fun j : Fin S.n =>
    (List.ofFn fun i : Fin (S.data.μ j) => ratCode (s ⟨j, i⟩)).flatten).flatten

/-- Rational start, finish, piece count, then endpoints, for each operation.
No bound on the number of pieces is imposed except the algorithm's bit time. -/
def pieceCode (S : RationalShop) (s : PieceSchedule S.data) : List Bool :=
  (List.ofFn fun j : Fin S.n =>
    (List.ofFn fun i : Fin (S.data.μ j) =>
      let o : S.data.Op := ⟨j, i⟩
      ratCode (s.begin o) ++ ratCode (s.finish o) ++ natCode (s.pieces o).length ++
        (s.pieces o).flatMap (fun ab => ratCode ab.1 ++ ratCode ab.2)).flatten).flatten

/-- Scheduling promise input includes a positive rational objective threshold. -/
def thresholdCode (S : RationalShop) (b : ℚ) : List Bool := shopCode S ++ ratCode b

end FlowJobHardness.FlowShopGap.Supplement


