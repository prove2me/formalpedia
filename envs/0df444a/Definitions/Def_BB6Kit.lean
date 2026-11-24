-- Prove2me | Definitions.Def_BB6Kit
-- name    : BB6Kit
-- status  : Definition
-- author  : @alon yuval
-- created : 2026-11-23T22:12:09.972804+00:00
-- url     : https://prove2.me/theorems/4ed116e9-41a1-4827-b3d1-58a894200373
-- title:
--   Mignotte–Voutier kit: rows, columns, $g$, $G_i$, $M_i$, $b$, $\Lambda'$, and an explicit parameter family
-- statement:
--   Notation of the Mignotte–Voutier kit for linear forms in three logarithms (arXiv:2205.08899, Section 2.2), for positive-integer $\alpha_1,\alpha_2,\alpha_3$:
--
--   - `MultIndep a1 a2 a3`: $a_1^x a_2^y a_3^z = 1$ with $x,y,z\in\mathbb Z$ forces $x=y=z=0$.
--   - `rowSet K L`: the triples $(k,m,\ell)$ with $k+m\le K-1$, $0\le\ell\le L-1$ (there are $N=K(K+1)L/2$ of them). `RowsOK`: the rows $(k_i,m_i,\ell_i)$ are $N$ distinct such triples. `ColsOK`: the columns $(r_j,s_j,t_j)$ are $N$ distinct triples with $r_j<R$, $s_j<S$, $t_j<T$.
--   - `gK` $= g = \tfrac14 - \tfrac{N}{12RST}$ and `GK` $= G = NLXg/2$ for $X=R,S,T$ (eq. (2.2)).
--   - `MK` $= M = \tfrac{L-1}{2}\sum_j c(r_j,s_j,t_j)$; with $c$ a coordinate projection these are $M_1,M_2,M_3$.
--   - `bK` is the quantity $b$ of (2.5): $b=(b'_3\eta_0)(b''_3\zeta_0)\bigl(\prod_{k=1}^{K-1}(k!)^{K-k}\bigr)^{-12/(K(K-1)(K+1))}$ with $\eta_0=(R-1)/2+\beta_1(T-1)/2$, $\zeta_0=(S-1)/2+\beta_2(T-1)/2$.
--   - `lamPrime` $= \Lambda' = |\Lambda|\cdot LT e^{LT|\Lambda|/(2b_3)}/(2b_3)$ (Theorem 2.1).
--
--   It also fixes an explicit parameter family used for the BB(6) instance $\alpha=(2,c,3)$, $b=(k-1,1,i)$, indexed by $n=\lfloor\log_2 i\rfloor$: $K=2^{23}n^2$, $L=8n$, $R_1=T_1=K/8$, $S_1=80$, $R_2=T_2=K/64$, $S_2=2^{15}n$, $R_3=T_3=K/32$, $S_3=2^{15}n$, $R=T=R_1+R_2+R_3+1$, $S=S_1+S_2+S_3+1$, $M_0=\lfloor(V_1-1)/K\rfloor$ with $V_1=(R_1+1)(S_1+1)(T_1+1)$, and $\chi=M_0/\sqrt{V_1}$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 2.2 (eqs. (2.2)-(2.5)) and Theorem 2.1; parameter family new (BB(6) Baker roadmap).

import Mathlib
import Definitions.Def_BB6Delta

namespace BB6Kit

/-- Multiplicative independence of three positive integers: `a1^x a2^y a3^z = 1` with integer exponents forces `x = y = z = 0`. -/
def MultIndep (a1 a2 a3 : ℕ) : Prop :=
  ∀ x y z : ℤ, (a1 : ℝ) ^ x * (a2 : ℝ) ^ y * (a3 : ℝ) ^ z = 1 → x = 0 ∧ y = 0 ∧ z = 0

/-- Row index set of the Mignotte–Voutier kit (Sec. 2.2): triples `(k, m, ℓ)` with `k + m ≤ K - 1`, `ℓ ≤ L - 1`. -/
def rowSet (K L : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range K ×ˢ Finset.range K ×ˢ Finset.range L).filter (fun x => x.1 + x.2.1 ≤ K - 1)

/-- The rows `(kᵢ, mᵢ, ℓᵢ)` are `N` distinct elements of `rowSet K L` (with `N = K(K+1)L/2` they enumerate it). -/
def RowsOK (K L N : ℕ) (kml : Fin N → ℕ × ℕ × ℕ) : Prop :=
  Function.Injective kml ∧ ∀ n, kml n ∈ rowSet K L

/-- The columns `(rⱼ, sⱼ, tⱼ)` are `N` distinct triples with `rⱼ < R`, `sⱼ < S`, `tⱼ < T`. -/
def ColsOK (R S T N : ℕ) (rst : Fin N → ℕ × ℕ × ℕ) : Prop :=
  Function.Injective rst ∧ ∀ j, (rst j).1 < R ∧ (rst j).2.1 < S ∧ (rst j).2.2 < T

/-- `g = 1/4 - N/(12RST)` of (2.2). -/
noncomputable def gK (N R S T : ℕ) : ℝ := 1 / 4 - (N : ℝ) / (12 * (R : ℝ) * S * T)

/-- `G = N L X g / 2` of (2.2), with `X = R, S, T` giving `G₁, G₂, G₃`. -/
noncomputable def GK (N L R S T X : ℕ) : ℝ := (N : ℝ) * L * X * gK N R S T / 2

/-- `M = (L-1)/2 · Σⱼ c(rⱼ, sⱼ, tⱼ)`; with `c` a coordinate projection this is `M₁, M₂, M₃` of Sec. 2.2. -/
noncomputable def MK (L N : ℕ) (rst : Fin N → ℕ × ℕ × ℕ) (c : ℕ × ℕ × ℕ → ℕ) : ℝ :=
  ((L : ℝ) - 1) / 2 * ∑ j, (c (rst j) : ℝ)

/-- The quantity `b` of (2.5), with `η₀ = (R-1)/2 + β₁(T-1)/2`, `ζ₀ = (S-1)/2 + β₂(T-1)/2`,
`β₁ = b′₁/b′₃`, `β₂ = b″₂/b″₃`. -/
noncomputable def bK (K R S T b1' b3' b2'' b3'' : ℕ) : ℝ :=
  ((b3' : ℝ) * (((R : ℝ) - 1) / 2 + (b1' : ℝ) / b3' * (((T : ℝ) - 1) / 2))) *
  ((b3'' : ℝ) * (((S : ℝ) - 1) / 2 + (b2'' : ℝ) / b3'' * (((T : ℝ) - 1) / 2))) *
  (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) ^ (-(12 : ℝ) / ((K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1)))

/-- `Λ′ = |Λ| · L T e^{L T |Λ| / (2 b₃)} / (2 b₃)` of Theorem 2.1. -/
noncomputable def lamPrime (L T b3 : ℕ) (Λ : ℝ) : ℝ :=
  |Λ| * ((L : ℝ) * T * Real.exp ((L : ℝ) * T * |Λ| / (2 * (b3 : ℝ)))) / (2 * (b3 : ℝ))

/-! Explicit parameter family for `α = (2, c, 3)`, `b = (k-1, 1, i)`, indexed by `n = ⌊log₂ i⌋`. -/
def fK (n : ℕ) : ℕ := 2 ^ 23 * n ^ 2
def fL (n : ℕ) : ℕ := 8 * n
def fR1 (n : ℕ) : ℕ := fK n / 8
def fS1 (_n : ℕ) : ℕ := 80
def fR2 (n : ℕ) : ℕ := fK n / 64
def fS2 (n : ℕ) : ℕ := 2 ^ 15 * n
def fR3 (n : ℕ) : ℕ := fK n / 32
def fS3 (n : ℕ) : ℕ := 2 ^ 15 * n
def fR (n : ℕ) : ℕ := fR1 n + fR2 n + fR3 n + 1
def fS (n : ℕ) : ℕ := fS1 n + fS2 n + fS3 n + 1
def fN (n : ℕ) : ℕ := fK n * (fK n + 1) * fL n / 2
/-- `M₀ = ⌊(V₁ - 1)/K⌋` with `V₁ = (R₁+1)(S₁+1)(T₁+1)`, `T₁ = R₁`; the parameter `χ` is `M₀ / √V₁`. -/
def fM0 (n : ℕ) : ℕ := ((fR1 n + 1) * (fS1 n + 1) * (fR1 n + 1) - 1) / fK n
noncomputable def fChi (n : ℕ) : ℝ := (fM0 n : ℝ) / Real.sqrt (((fR1 n + 1) * (fS1 n + 1) * (fR1 n + 1) : ℕ) : ℝ)

end BB6Kit


