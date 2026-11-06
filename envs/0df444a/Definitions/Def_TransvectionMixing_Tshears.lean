-- Prove2me | Definitions.Def_TransvectionMixing_Tshears
-- name    : TransvectionMixing_Tshears
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:27.5122+00:00
-- url     : https://prove2.me/theorems/fe59196f-8056-4386-af55-a461d3ad0279
-- title:
--   Thresholds $Q_{\mathrm{all}}$, $Q_{\mathrm{geom}}$, the degree bound $H(T,\eta)$ and the schedule length $T_{\mathrm{shears}}(\eta)$
-- statement:
--   The constants of the paper, with natural logarithms throughout:
--
--   1. the common field threshold $Q_{\mathrm{all}}(n)=(5000n)^{6n^2}$;
--   2. $Q_{\mathrm{geom}}(H,m;\varepsilon)=256\,\varepsilon^{-4}H^{13m/3}$;
--   3. the coefficient-degree bound
--   $$
--   H(T,\eta)=\min\Bigl\{T,\ \Bigl\lceil \frac{eT}{n}+\log\frac{16n}{\eta}\Bigr\rceil\Bigr\};
--   $$
--   4. the four-shear schedule: $\lambda=\min\{1,\sqrt{(9/n)\log(3n/\eta)}\}$,
--   $$
--   N^{\mathrm{out}}=\Bigl\lceil n(n-1)\bigl((1-\lambda)\log 2+\lambda\log 5\bigr)+2(n-1)\log\tfrac{3n}{\eta}\Bigr\rceil,\qquad
--   N^{\mathrm{mid}}=\Bigl\lceil n(n-1)\lambda\log 5+2(n-1)\log\tfrac{3n}{\eta}\Bigr\rceil,
--   $$
--   and $T_{\mathrm{shears}}(\eta)=4(2N^{\mathrm{out}}+N^{\mathrm{mid}})$.
--
--   **Formalization Note** $H$ and $m$ in $Q_{\mathrm{geom}}$ are real numbers, so that $m=n^2-1$ involves no natural-number subtraction; every theorem using it states the paper's ranges. Ceilings are `Nat.ceil`, whose arguments are positive in every use.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Theorem 1.1, p.4 (Q_all); eq. (13), p.12 (Q_geom); eq. (6), p.9 (H); eqs. (33)–(35), p.28 (λ, N^out, N^mid, T_shears)

import Mathlib

namespace TransvectionMixing

/-- The common field threshold `Q_all(n) = (5000n)^{6n²}` (Braverman–Jain–Newman, *Optimal
Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields*, manuscript sha256
217f833f…, Theorem 1.1, p.4). -/
noncomputable def Qall (n : ℕ) : ℝ := (5000 * (n : ℝ)) ^ (6 * n ^ 2)

/-- `Q_geom(H, m; ε) = 256 ε⁻⁴ H^{13m/3}` (manuscript sha256 217f833f…, eq. (13), p.12).

**Formalization Note** `H` and `m` are real so that `m = n² − 1` needs no natural
subtraction; the paper uses it for `H ≥ 2`, integer `m ≥ 1`, `0 < ε ≤ 1/4`, and every
theorem of the mission states those ranges. The power is `Real.rpow`. -/
noncomputable def Qgeom (H m ε : ℝ) : ℝ := 256 / ε ^ 4 * H ^ (13 * m / 3)

/-- The degree bound `H(T, η) = min{T, ⌈eT/n + log(16n/η)⌉}` (manuscript sha256 217f833f…,
eq. (6), p.9; natural logarithm). -/
noncomputable def Hdeg (n T : ℕ) (η : ℝ) : ℕ :=
  min T ⌈Real.exp 1 * T / n + Real.log (16 * n / η)⌉₊

/-- `λ = min{1, √((9/n) log(3n/η))}` (manuscript sha256 217f833f…, eq. (33), p.28). -/
noncomputable def shearLambda (n : ℕ) (η : ℝ) : ℝ :=
  min 1 (Real.sqrt (9 / n * Real.log (3 * n / η)))

/-- `N^out = ⌈n(n−1)((1−λ) log 2 + λ log 5) + 2(n−1) log(3n/η)⌉` (manuscript sha256
217f833f…, eq. (34), p.28). -/
noncomputable def Nout (n : ℕ) (η : ℝ) : ℕ :=
  ⌈(n : ℝ) * (n - 1) * ((1 - shearLambda n η) * Real.log 2 + shearLambda n η * Real.log 5)
      + 2 * ((n : ℝ) - 1) * Real.log (3 * n / η)⌉₊

/-- `N^mid = ⌈n(n−1) λ log 5 + 2(n−1) log(3n/η)⌉` (manuscript sha256 217f833f…, eq. (34),
p.28). -/
noncomputable def Nmid (n : ℕ) (η : ℝ) : ℕ :=
  ⌈(n : ℝ) * (n - 1) * shearLambda n η * Real.log 5 + 2 * ((n : ℝ) - 1) * Real.log (3 * n / η)⌉₊

/-- The four-shear schedule length `T_shears(η) = 4(2N^out + N^mid)` (manuscript sha256
217f833f…, eq. (35), p.28). -/
noncomputable def Tshears (n : ℕ) (η : ℝ) : ℕ := 4 * (2 * Nout n η + Nmid n η)

end TransvectionMixing


