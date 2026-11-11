-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Params
-- name    : BlottoFPTAS_Main_Params
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:41:49.346208+00:00
-- url     : https://prove2.me/theorems/399a1c5a-a23d-40de-adce-2e8536536ff0
-- title:
--   The parameters of §5 and Appendix C.2 as functions of m and e = 2^(−a), and the candidate bids S of Appendix C.3
-- statement:
--   The construction uses $e=2^{-a}$ for an integer $a\ge1$ with $\varepsilon/2<e\le\varepsilon$. With $m$ the number of reduced battlefields, App. C.2 sets
--   $$z=\tfrac{e}{2048},\ K=\tfrac{128}e,\ S=\mathrm{pow2ceil}\big(\tfrac{128m}e\big),\ d=m(K-1),\ H=(m+3)^{d+2},\ Q_g=\mathrm{pow2ceil}(4H^2),\ q=2Q_g,$$
--   $$J_D=m\big(\tfrac{64}z-1\big)+1,\ D=q(m+2)^{J_D},\ C=\mathrm{pow2ceil}(4D^2),\ 2^\Lambda=8C,$$
--   $k_{\mathrm{ep}}=1/z$, $M_{\mathrm{ep}}=\mathrm{pow2ceil}(2^{24}(\Lambda+2)/z)$ and $T=M_{\mathrm{ep}}k_{\mathrm{ep}}$; §5.1 and §5.4 use $k=8/e$ representative battlefields and $S_{\mathrm{out}}=\mathrm{pow2ceil}(64/e)$ shifts. The **candidate bids** are $S=F_D\cup\{t/C:t=0,\dots,C\}$, with $F_D$ the rationals in $[0,1]$ of reduced denominator at most $D$ (App. C.3), and the **candidate allocations** for budget $c$ are $X=\{x\in S^m:\sum_jx_j\le c\}$.
--
--   **Formalization Note.** Every quantity written $c/e$ or $c/z$ is a power of two times $2^a$ and is a natural number here.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 30 (e); pp. 55–56, App. C.2; p. 57, App. C.3

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Sizes

namespace BlottoFPTAS.Main

/-!
# Parameters of §5 and Appendix C.2 (pp. 30–31, 55–57)

The approximation parameter is `e = 2^{-a}` for an integer `a ≥ 1` with `ε/2 < e ≤ ε` (p. 30).
Every parameter below is a function of the number `m` of reduced battlefields and of `a` only
(App. C.2, pp. 55–56); quantities that the paper writes as `c/e` or `c/z` are powers of two times
`2^a` and are written as natural numbers.

| paper | here | value |
|---|---|---|
| `e` | `eR a` | `2^{-a}` |
| `z` | `zR a` | `e/2048` |
| `K` | `Klab a` | `128/e = 2^{a+7}` |
| `S` | `Sscore m a` | `pow2ceil(128m/e)` |
| `d` | `dAnch m a` | `m(K − 1)` |
| `H` | `Hbd m a` | `(m+3)^{d+2}` |
| `Q_g` | `Qg m a` | `pow2ceil(4H²)` |
| `q` | `qDen m a` | `2Q_g` |
| `K′` | `Kprime a` | `64/z` |
| `J_D` | `JD m a` | `m(64/z − 1) + 1` |
| `D` | `Dden m a` | `q (m+2)^{J_D}` |
| `C` | `Cgrid m a` | `pow2ceil(4D²)` |
| `Λ` | `Lam m a` | `log₂(8C)` (`U_code = 8C = 2^Λ`) |
| `k_ep` | `kEp a` | `1/z` |
| `M_ep` | `Mep m a` | `pow2ceil(2^24 (Λ+2)/z)` |
| `T` | `Titer m a` | `M_ep k_ep` |
| `k` | `kRep a` | `8/e`, the number of representative battlefields (§5.1) |
| `S_out` | `Sout a` | `pow2ceil(64/e)`, the number of finite shifts (§5.4) |

The candidate bids (App. C.3, p. 57) are `S = F_D ∪ {t/C : t = 0, …, C}`, where `F_D` is the set of
rationals in `[0, 1]` with reduced denominator at most `D`.
-/

/-- `e = 2^{-a}`. -/
noncomputable def eR (a : ℕ) : ℝ := 1 / 2 ^ a

/-- `z = e/2048`. -/
noncomputable def zR (a : ℕ) : ℝ := eR a / 2048

/-- `K = 128/e`, labels per battlefield. -/
def Klab (a : ℕ) : ℕ := 2 ^ (a + 7)

instance (a : ℕ) : NeZero (Klab a) := ⟨by unfold Klab; positivity⟩

/-- `S = pow2ceil(128m/e)`, the score scale. -/
def Sscore (m a : ℕ) : ℕ := pow2ceil (128 * m * 2 ^ a)

/-- `d = m(K − 1)`, the number of anchors of nonzero labels. -/
def dAnch (m a : ℕ) : ℕ := m * (Klab a - 1)

/-- `H = (m + 3)^{d+2}`. -/
def Hbd (m a : ℕ) : ℕ := (m + 3) ^ (dAnch m a + 2)

/-- `Q_g = pow2ceil(4H²)`. -/
def Qg (m a : ℕ) : ℕ := pow2ceil (4 * Hbd m a ^ 2)

/-- `q = 2 Q_g`, the bound on the denominator of `ρ`. -/
def qDen (m a : ℕ) : ℕ := 2 * Qg m a

/-- `K′ = 64/z = 2^{a+17}`. -/
def Kprime (a : ℕ) : ℕ := 64 * 2048 * 2 ^ a

/-- `J_D = m(64/z − 1) + 1`. -/
def JD (m a : ℕ) : ℕ := m * (Kprime a - 1) + 1

/-- `D = q (m + 2)^{J_D}`. -/
def Dden (m a : ℕ) : ℕ := qDen m a * (m + 2) ^ JD m a

/-- `C = pow2ceil(4D²)`. -/
def Cgrid (m a : ℕ) : ℕ := pow2ceil (4 * Dden m a ^ 2)

/-- `Λ = log₂(8C)`; the code set is `I = {0, …, 2^Λ − 1}`. -/
def Lam (m a : ℕ) : ℕ := Nat.log 2 (8 * Cgrid m a)

/-- `k_ep = 1/z`, iterations per epoch. -/
def kEp (a : ℕ) : ℕ := 2048 * 2 ^ a

/-- `M_ep = pow2ceil(2^24 (Λ + 2)/z)`, the number of epochs. -/
def Mep (m a : ℕ) : ℕ := pow2ceil (2 ^ 24 * (Lam m a + 2) * kEp a)

/-- `T = M_ep k_ep`, the number of iterations (a power of two). -/
def Titer (m a : ℕ) : ℕ := Mep m a * kEp a

/-- `k = 8/e`, the number of representative battlefields. -/
def kRep (a : ℕ) : ℕ := 2 ^ (a + 3)

/-- `S_out = pow2ceil(64/e)`, the number of finite shifts. -/
def Sout (a : ℕ) : ℕ := pow2ceil (64 * 2 ^ a)

/-- The candidate bids `S = F_D ∪ {t/C : t = 0, …, C}` (App. C.3, p. 57). -/
def candSet (m a : ℕ) : Set ℚ :=
  {s | 0 ≤ s ∧ s ≤ 1 ∧ s.den ≤ Dden m a} ∪
    {s | ∃ t : ℕ, t ≤ Cgrid m a ∧ s = (t : ℚ) / Cgrid m a}

/-- The candidate allocations `X = {x ∈ S^m : ∑_j x_j ≤ c}` (p. 33). -/
def candAllocs (m a : ℕ) (c : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ j, ∃ s ∈ candSet m a, x j = (s : ℝ)) ∧ ∑ j, x j ≤ c}

end BlottoFPTAS.Main


