-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Reuse
-- name    : TDHamSim_QueryOptimal_Reuse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:18:25.401821+00:00
-- url     : https://prove2.me/theorems/6506348f-7dfc-4bfb-b482-a369ca587770
-- title:
--   Finite reuse circuits and signed combination coefficients
-- statement:
--   A reuse register has $b$ qubits, and a length $N$ satisfies $1\le N<2^b$. A concrete real Householder completion prepares the uniform state on its first $N$ labels. The increment acts only on the private summand, and call $\ell$ applies the query, the update conditioned on reuse label $\ell$, and that increment, in order. The resulting circuit $V_N$ defines $P_N$ by zero-register compression.
--
--   $$E_q(z)=Q(z)^qG_{2q}(z),\qquad\lambda_N=N(e_{N-1}-e_N),\qquad\Lambda=\sum_{N=1}^{4q}|\lambda_N|.$$
--
--   The monomial coefficients $e_k$, the signed combination $\widetilde U$, arbitrary finite combinations, and the common register width are computed explicitly. The compression $P_N$ depends only on the uniform preparation column, so fixing its completion does not change the source operator.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), (30)–(34), pp.17–18; (52)–(55), p.23; (73), p.29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Cayley

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- A real Householder state preparation, fixing the identity case explicitly. -/
noncomputable def realPrep {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι) (v : ι → ℝ) : Mat ι :=
  let d : ι → ℝ := fun x => (if x = z then 1 else 0) - v x
  if ∀ x, d x = 0 then 1 else
    fun x y => (if x = y then 1 else 0) -
      ((2 * d x * d y / (∑ k, d k ^ 2) : ℝ) : ℂ)
noncomputable def uniformPrep (b N : ℕ) : Mat (Fin (2 ^ b)) :=
  realPrep ⟨0, pow_pos (by decide) _⟩
    (fun x => if x.val < N then (Real.sqrt N)⁻¹ else 0)

abbrev ReuseSpace (b J a n : ℕ) := Fin (2 ^ b) × Space J a n
noncomputable def prepPublic (b N J a n : ℕ) : Mat (ReuseSpace b J a n)
  | (k, Sum.inl x), (l, Sum.inl y) => if x = y then uniformPrep b N k l else 0
  | (k, Sum.inr x), (l, Sum.inr y) => if k = l ∧ x = y then 1 else 0
  | _, _ => 0
noncomputable def incrementPrivate (b J a n : ℕ) : Mat (ReuseSpace b J a n)
  | (k, Sum.inl x), (l, Sum.inl y) => if k = l ∧ x = y then 1 else 0
  | (k, Sum.inr x), (l, Sum.inr y) =>
      if k.val = (l.val + 1) % (2 ^ b) ∧ x = y then 1 else 0
  | _, _ => 0
noncomputable def reuseStep {J a n : ℕ} (b ℓ : ℕ) (w : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Mat (ReuseSpace b J a n) :=
  incrementPrivate b J a n *
    (Matrix.of fun x y : ReuseSpace b J a n => if x.1 = y.1 then
      if x.1.val = ℓ then updates J a n w x.2 y.2 else (1 : Mat (Space J a n)) x.2 y.2
      else 0) *
    (Matrix.of fun x y : ReuseSpace b J a n => if x.1 = y.1 then querySum O x.2 y.2 else 0)
noncomputable def reuseV {J a n : ℕ} (b N : ℕ) (w : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Mat (ReuseSpace b J a n) := by
  classical
  exact (prepPublic b N J a n).conjTranspose *
    ((List.range N).map (fun ℓ => reuseStep b ℓ w O)).foldl (fun acc U => U * acc) (1 : Mat (ReuseSpace b J a n)) *
    prepPublic b N J a n
noncomputable def reuseP {J a n : ℕ} (b N : ℕ) (w : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Mat (Bits n) :=
  fun x y => reuseV b N w O (⟨0, pow_pos (by decide) _⟩, Sum.inl x)
    (⟨0, pow_pos (by decide) _⟩, Sum.inl y)

noncomputable def combine {J a n L : ℕ} (b : ℕ) (w : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) (coeff : Fin L → ℝ) : Mat (Bits n) :=
  ∑ r, (coeff r : ℂ) • reuseP b (r.val + 1) w O
noncomputable def combinedG {ι : Type} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (coeff : Fin L → ℝ) (A : Mat ι) : Mat ι :=
  ∑ r, (coeff r : ℂ) • G (r.val + 1) A

noncomputable def bCoeff (q j : ℕ) : ℝ := (2 : ℝ)^(-(q : ℤ)) * Nat.choose q j
noncomputable def errorPolynomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (A : Mat ι) : Mat ι := Q A ^ q * G (2*q) A

/-- The monomial coefficients of Q(z)^q G_(2q)(z), including e_(4q)=0. -/
noncomputable def eCoeff (q k : ℕ) : ℝ :=
  (2 * q : ℝ)⁻¹ * ∑ j ∈ Finset.range (q + 1),
    if 2 * j ≤ k ∧ k - 2 * j < 2 * q then bCoeff q j else 0
noncomputable def lambda (q N : ℕ) : ℝ := (N : ℝ) * (eCoeff q (N - 1) - eCoeff q N)
noncomputable def normalization (q : ℕ) : ℝ := ∑ r ∈ Finset.range (4 * q), |lambda q (r + 1)|
noncomputable def uTilde {J a n : ℕ} (q b : ℕ) (w : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Mat (Bits n) :=
  combine b w O (fun r : Fin (4 * q) => lambda q (r.val + 1))
def reuseWidth (q : ℕ) : ℕ := Nat.clog 2 (4 * q + 2)

end TDHamSim.QueryOptimal


