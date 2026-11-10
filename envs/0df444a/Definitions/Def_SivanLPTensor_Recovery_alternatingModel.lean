-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_alternatingModel
-- name    : SivanLPTensor_Recovery_alternatingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:30:52.1452+00:00
-- url     : https://prove2.me/theorems/66a228b6-0cd6-48b0-bf26-c31eba1fc6d6
-- title:
--   Unnormalized alternation, exterior contractions, and formula (5)
-- statement:
--   For columns $E=[e_1|\cdots|e_k]$, unnormalized alternation is
--   $$\operatorname{Alt}(E)=\sum_{\sigma\in S_k}\operatorname{sgn}(\sigma)e_{\sigma(1)}\otimes\cdots\otimes e_{\sigma(k)}.$$
--   The tensor-power arrays use the standard coordinate basis. Contraction applies the covectors in their row order, leaving the final two tensor indices ordered. The alternating square $x\otimes y-y\otimes x$ is represented by $xy^\top-yx^\top$.
--   The mathematical contraction $\Omega_P(T)=\iota_P\operatorname{Alt}(\bar T)$ is defined independently of the signed-deleted-minor expression. A separate formula sums the input coordinates and pairs of retained columns with coefficient $(-1)^{j+k+1}\det(PE_\alpha[\widehat{j,k}])$. Zero-based indices have the same parity exponent. The identities connecting these definitions are theorem obligations; this file assumes none of them.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), §2.1 and Definition 3.1, printed pp. 4–6 / PDF pp. 6–8, (3)–(5)

import Definitions.Def_SivanLPTensor_Recovery_tensorModel

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators
open Finset

abbrev TensorPower (I : Type) (k : ℕ) := (Fin k → I) → ℝ

/-- Unnormalized alternation in the dense standard tensor basis. -/
def alt {I : Type} [Fintype I] {k : ℕ} (E : Matrix I (Fin k) ℝ) : TensorPower I k :=
  fun α => ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ∏ j, E (α j) (σ j)

/-- Exterior contraction, with p₁ applied first. The residual two entries stay ordered. -/
def contract {I : Type} [Fintype I] {d : ℕ}
    (P : Matrix (Fin d) I ℝ) (w : TensorPower I (d + 2)) : Matrix I I ℝ :=
  fun x y => ∑ β : Fin d → I, (∏ t, P t (β t)) *
    w (Fin.append β (fun j : Fin 2 => if j = 0 then x else y))

def altTwo {I : Type} (x y : I → ℝ) : Matrix I I ℝ :=
  fun u v => x u * y v - y u * x v

/-- The ascending column order left after deleting j,k. -/
def remaining (m : ℕ) (j k : Fin m) : List (Fin m) :=
  (List.finRange m).filter (fun t => t ≠ j ∧ t ≠ k)

def deletedMinor {I : Type} [Fintype I] {d : ℕ}
    (P : Matrix (Fin d) I ℝ) (E : Matrix I (Fin (d + 2)) ℝ)
    (j k : Fin (d + 2)) : Matrix (Fin d) (Fin d) ℝ :=
  fun t s => ∑ x, P t x * E x ((remaining (d + 2) j k)[s.val]?.getD 0)

/-- Formula (3), in zero-based indices; the sign is still (-1)^(j+k+1). -/
def minorContraction {I : Type} [Fintype I] {d : ℕ}
    (P : Matrix (Fin d) I ℝ) (E : Matrix I (Fin (d + 2)) ℝ) : Matrix I I ℝ :=
  ∑ j, ∑ k ∈ univ.filter (fun k => j < k),
    ((-1 : ℝ) ^ (j.val + k.val + 1) * Matrix.det (deletedMinor P E j k)) •
      altTwo (fun x => E x j) (fun x => E x k)

def standardFrame {m : ℕ} {n : Fin m → ℕ}
    (α : (j : Fin m) → Fin (n j)) : Matrix (BlockIndex n) (Fin m) ℝ :=
  fun x j => if x.1 = j ∧ x.2.val = (α j).val then 1 else 0

/-- The embedded, alternated input, defined independently of the determinant formula. -/
def altInput {m : ℕ} {n : Fin m → ℕ} (T : Tensor n) : TensorPower (BlockIndex n) m :=
  ∑ α, T α • alt (standardFrame α)

def omega {d : ℕ} {n : Fin (d + 2) → ℕ}
    (T : Tensor n) (P : Matrix (Fin d) (BlockIndex n) ℝ) :
    Matrix (BlockIndex n) (BlockIndex n) ℝ := contract P (altInput T)

/-- Formula (5): depends only on the dense input and the covector frame. -/
def omegaFormula {d : ℕ} {n : Fin (d + 2) → ℕ}
    (T : Tensor n) (P : Matrix (Fin d) (BlockIndex n) ℝ) :
    Matrix (BlockIndex n) (BlockIndex n) ℝ :=
  ∑ α, T α • minorContraction P (standardFrame α)

end SivanLPTensor.Recovery


