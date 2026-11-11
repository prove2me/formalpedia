-- Prove2me | Definitions.Def_SubexpPermanent_Main_Objective
-- name    : SubexpPermanent_Main_Objective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:02:23.618013+00:00
-- url     : https://prove2.me/theorems/59299f73-7012-48e7-b498-f5c3535133a6
-- title:
--   The objective $\Phi_A$, the budget sets $D_a$, $\mathrm{OPT}_A(a)$, $H(x)$, the normalized weights $w(x,a)$, $F_A$, $p^{(v)}$ and $\hat A$
-- statement:
--   For a nonnegative real $n\times n$ matrix $A$ with edge set $E$ and $y\in\mathbb R^E$, the objective (4) is
--   $$\Phi_A(y)=\log Z(e^y)+\max_{M\text{ perfect matching}}\ \sum_{e\in M}(\log A_e-y_e),$$
--   where $Z(e^y)$ sums over all matchings using edges in $E$ and the maximum runs over perfect matchings using edges in $E$. For $a\in\mathbb R$ the **budget set** is $D_a=\{y\in\mathbb R^E:\sum_{e\ni v}e^{y_e}\le e^a\text{ for every vertex }v\}$, and
--   $$\mathrm{OPT}_A(a)=\inf_{y\in D_a}\Phi_A(y)$$
--   (eq. (5); Lemma 6.2 proves that the infimum is a minimum). For $x\in\mathbb R^E$ let $H(x)=\max_v\log\sum_{e\ni v}e^{x_e}$ and $w_e(x,a)=e^{x_e+a-H(x)}$ (24), and
--   $$F_A(x,a)=\Phi_A(\log w(x,a))=\Phi_A\big(x+(a-H(x))\mathbf 1\big)\qquad(25).$$
--   For a vertex $v$, $p^{(v)}_e=w_e(x,a)/e^a$ on the edges incident to $v$ and $p^{(v)}_e=0$ otherwise. For §8, given a set $E_0$ of pairs and $\theta\in\mathbb Q^{E_0}$, $\hat A_{ij}=e^{\theta_{ij}}$ on $E_0$ and $0$ elsewhere.
--
--   **Formalization Note.** The maximum over perfect matchings is a `Finset.sup'` over the permutations that use only edges of $E$; it is set to $0$ when there is none, a case every statement excludes by $\operatorname{per}(A)>0$. $\mathrm{OPT}_A(a)$ is the real infimum `⨅` over $D_a$; it would be the junk value $0$ only if $\Phi_A$ were unbounded below on $D_a$, which Lemma 6.2 rules out. $H$ is a real `⨆` over the $2n$ vertices, a genuine maximum for $n\ge1$. Each vertex has an incident edge when $\operatorname{per}(A)>0$, so no logarithm of $0$ occurs.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 4 eqs. (4)–(5), p. 20 (§6), p. 22 eqs. (24)–(25) and Lemma 6.4, p. 29 (§8)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_PermanentGraph

namespace SubexpPermanent.Main

/-! # The objective `Φ_A`, the budget sets `D_a`, `OPT_A`, and the normalized objective `F_A`
(Kudria–Luo–Majid, eqs. (4), (5) p. 4; §6 p. 20; eqs. (24), (25) p. 22; §8 p. 29) -/

open Classical

variable {n : ℕ}

/-- `max_{M perfect} ∑_{e ∈ M} (log A_e − y_e)`, the maximum over perfect matchings using edges
of `E` of `⟨log A − y, 1_M⟩` (`0` when `A` has no such matching, a case every statement
excludes by `per(A) > 0`). -/
noncomputable def compensation (A : Matrix (Fin n) (Fin n) ℝ) (y : Edges A → ℝ) : ℝ :=
  if h : (Finset.univ.filter (IsPerfMatching A)).Nonempty then
    (Finset.univ.filter (IsPerfMatching A)).sup' h
      (fun σ => dotProduct (logA A - y) (incVec A σ))
  else 0

/-- `Φ_A(y) = log Z(e^y) + max_{M perfect} ∑_{e∈M} (log A_e − y_e)`, eq. (4). -/
noncomputable def Phi (A : Matrix (Fin n) (Fin n) ℝ) (y : Edges A → ℝ) : ℝ :=
  Real.log (ZA A y) + compensation A y

/-- `D_a = {y ∈ ℝ^E : ∑_{e∋v} e^{y_e} ≤ e^a for every vertex v}`. -/
def budgetSet (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : Set (Edges A → ℝ) :=
  {y | ∀ v : Fin n ⊕ Fin n, vertexSum A y v ≤ Real.exp a}

/-- `OPT_A(a)`, the infimum of `Φ_A` over `D_a` (eq. (5); that it is attained is Lemma 6.2). -/
noncomputable def OPT (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : ℝ :=
  ⨅ y : budgetSet A a, Phi A y

/-- `H(x) = max_v log ∑_{e∋v} e^{x_e}`, eq. (24) (a maximum over the `2n` vertices). -/
noncomputable def Hmax (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ) : ℝ :=
  ⨆ v : Fin n ⊕ Fin n, Real.log (vertexSum A x v)

/-- `log w(x, a) = x + (a − H(x)) 1`, the logarithm of the normalized weights of eq. (24). -/
noncomputable def logNormWeight (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ) (a : ℝ) :
    Edges A → ℝ :=
  fun e => x e + (a - Hmax A x)

/-- `w_e(x, a) = e^{x_e + a − H(x)}`, eq. (24). -/
noncomputable def normWeight (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ) (a : ℝ) :
    Edges A → ℝ :=
  fun e => Real.exp (logNormWeight A x a e)

/-- `F_A(x, a) = Φ_A(log w(x, a)) = Φ_A(x + (a − H(x)) 1)`, eq. (25). -/
noncomputable def F (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ) (a : ℝ) : ℝ :=
  Phi A (logNormWeight A x a)

/-- The probability vector `p^{(v)}` of Lemma 6.4: `p^{(v)}_e = w_e(x, a)/e^a` for edges
incident to `v` and `0` otherwise. -/
noncomputable def pVec (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ) (a : ℝ)
    (v : Fin n ⊕ Fin n) : Edges A → ℝ :=
  fun e => if Incident e v then normWeight A x a e / Real.exp a else 0

/-- `Â` of §8 (p. 29): `Â_ij = e^{θ_ij}` on the edge set `E₀` and `0` elsewhere, for
`θ ∈ ℚ^{E₀}`. -/
noncomputable def hatMatrix (E₀ : Finset (Fin n × Fin n)) (θ : E₀ → ℚ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : (i, j) ∈ E₀ then Real.exp (θ ⟨(i, j), h⟩) else 0

end SubexpPermanent.Main


