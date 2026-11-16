-- Prove2me | Definitions.Def_ElimAgree_Supplement_SignOp
-- name    : ElimAgree_Supplement_SignOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:33:42.105844+00:00
-- url     : https://prove2.me/theorems/75485c3d-34df-4f86-a7a5-a622412f64b1
-- title:
--   The normalized sign operator $H_\mu$, balance, and inner product $\mathrm{IP}_n$
-- statement:
--   Let $\mu=\mu_X\times\mu_Y$ be a product of probability distributions on finite sets $\mathcal X,\mathcal Y$, and $f:\mathcal X\times\mathcal Y\to\{0,1\}$ with sign matrix $h=(-1)^f$. The **normalized sign operator** $H_\mu$ maps $b:\mathcal Y\to\mathbb R$ to
--
--   $$(H_\mu b)(x)=\mathbb E_{y\sim\mu_Y}\big[h(x,y)\,b(y)\big],$$
--
--   and $\|H_\mu\|$ is its norm from $L^2(\mu_Y)$ to $L^2(\mu_X)$, with the normalized inner products $\langle a,b\rangle=\mathbb E_\mu[ab]$:
--
--   $$\|H_\mu\|=\sup\Big\{\big(\mathbb E_{\mu_X}[(H_\mu b)^2]\big)^{1/2}:\ \mathbb E_{\mu_Y}[b^2]\le1\Big\}.$$
--
--   $h$ is **row balanced** if $\mathbb E_{y\sim\mu_Y}h(x,y)=0$ for every $x$, **column balanced** if $\mathbb E_{x\sim\mu_X}h(x,y)=0$ for every $y$, and **balanced** if both hold. The inner product function is $\mathrm{IP}_n(x,y)=\sum_jx_jy_j\bmod2$ on $\{0,1\}^n\times\{0,1\}^n$.
--
--   $\|H_\mu\|$ is the spectral quantity of the paper's lower bounds (Theorems 6.3, 7.2, C.2).
--
--   **Formalization Note** The supremum is a real `sSup` over a nonempty bounded set, so it is the operator norm also when $\mu$ lacks full support. $\{0,1\}$ is `Bool` with $1$ = `true`.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §2, p.6 (PDF p.8); Lemma 5.2, p.20 (PDF p.22); IP_n, p.2 (PDF p.4)

import Mathlib

namespace ElimAgree

namespace Supplement

/-!
# The normalized sign operator, balance, and inner product

Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript (STOC 2027 submission), §2, p.6; `IP_n`, p.2.

**Formalization Note.** A product measure `µ_X × µ_Y` on finite `X × Y` is a pair of laws
(`ElimAgree.IsLaw`). `L²(µ)` carries the normalized inner product `⟨a, b⟩ = E_µ[ab]`; the operator
norm is computed as a supremum over `b` with `E_{µ_Y}[b²] ≤ 1` of `(E_{µ_X}[(Hb)²])^{1/2}`. This set
is nonempty (`b = 0`) and bounded, so the real `sSup` is the operator norm, also when `µ` does not
have full support. `{0, 1}` is `Bool` with `1 = true`, so `h = (−1)^f` is `−1` where `f = true`.
-/

/-- The sign matrix `h = (−1)^f` (§2, p.6). -/
def hSign {X Y : Type} (f : X → Y → Bool) (x : X) (y : Y) : ℝ := if f x y then -1 else 1

/-- The operator with kernel `K` under `µ_Y` (§2, p.6): `(Tb)(x) = E_{y∼µ_Y}[K(x, y) b(y)]`. -/
noncomputable def opApply {X Y : Type} [Fintype Y] (μY : Y → ℝ) (K : X → Y → ℝ) (b : Y → ℝ)
    (x : X) : ℝ :=
  ∑ y, μY y * K x y * b y

/-- The norm of the operator with kernel `K` from `L²(µ_Y)` to `L²(µ_X)` (§2, p.6). -/
noncomputable def opNorm {X Y : Type} [Fintype X] [Fintype Y] (μX : X → ℝ) (μY : Y → ℝ)
    (K : X → Y → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ b : Y → ℝ, ∑ y, μY y * b y ^ 2 ≤ 1 ∧
    r = Real.sqrt (∑ x, μX x * opApply μY K b x ^ 2)}

/-- `∥H_µ∥`, the norm of the normalized sign operator, the operator with kernel `h = (−1)^f`
under `µ = µ_X × µ_Y` (§2, p.6). -/
noncomputable def signNorm {X Y : Type} [Fintype X] [Fintype Y] (μX : X → ℝ) (μY : Y → ℝ)
    (f : X → Y → Bool) : ℝ :=
  opNorm μX μY (hSign f)

/-- Row balance (§2, p.6; Lemma 5.2, p.20): `E_{y∼µ_Y} h(x, y) = 0` for every `x`. -/
def RowBalanced {X Y : Type} [Fintype Y] (μY : Y → ℝ) (f : X → Y → Bool) : Prop :=
  ∀ x, ∑ y, μY y * hSign f x y = 0

/-- Column balance: `E_{x∼µ_X} h(x, y) = 0` for every `y`. -/
def ColBalanced {X Y : Type} [Fintype X] (μX : X → ℝ) (f : X → Y → Bool) : Prop :=
  ∀ y, ∑ x, μX x * hSign f x y = 0

/-- `h = (−1)^f` is balanced under `µ_X × µ_Y` (§2, p.6): row and column balanced. -/
def Balanced {X Y : Type} [Fintype X] [Fintype Y] (μX : X → ℝ) (μY : Y → ℝ)
    (f : X → Y → Bool) : Prop :=
  RowBalanced μY f ∧ ColBalanced μX f

/-- Inner product `IP_n(x, y) = Σ_j x_j y_j mod 2` on `{0, 1}^n × {0, 1}^n` (p.2). -/
def ipFun (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter (fun j => x j && y j)).card % 2 = 1)

end Supplement

end ElimAgree


