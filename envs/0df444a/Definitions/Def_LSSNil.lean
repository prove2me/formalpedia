-- Prove2me | Definitions.Def_LSSNil
-- name    : LSSNil
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T17:59:16.506322+00:00
-- url     : https://prove2.me/theorems/06f83277-b0b7-45cb-aa45-f71ff67db0b0
-- title:
--   Nilmanifolds of bounded complexity, polynomial sequences and Lipschitz nilsequences (Green–Tao / Leng–Sah–Sawhney conventions)
-- statement:
--   Nilmanifolds, polynomial sequences and Lipschitz functions, following Definitions 2.3–2.7 and 3.1–3.5 of Leng–Sah–Sawhney (arXiv:2402.17994), which agree with those of Green–Tao (*The quantitative behaviour of polynomial orbits on nilmanifolds*).
--
--   Every connected, simply connected nilpotent Lie group $G$ is isomorphic to a group of unipotent upper triangular real matrices whose Lie algebra consists of strictly upper triangular matrices (Ado–Birkhoff), with the exponential map given by the terminating matrix exponential `mexp`. A structure `Nilmanifold s` (a nilmanifold $G/\Gamma$ of degree $s$) consists of:
--
--   * a Mal'cev basis $X_0,\dots,X_{d-1}$ of $\log G$ (linearly independent strictly upper triangular $n\times n$ matrices), with rational structure constants $[X_i,X_j]=\sum_k c_{ijk}X_k$ satisfying the Mal'cev ideal property $c_{ijk}\neq 0\Rightarrow \max(i,j)\le k$;
--   * a degree-$s$ filtration $G=G_0=G_1\supseteq G_2\supseteq\dots\supseteq G_{s+1}=\{\mathrm{id}\}$ adapted to the basis ($\log G_i=\mathrm{span}(X_j : j\ge d-\dim G_i)$) with $[\log G_i,\log G_j]\subseteq \log G_{i+j}$;
--   * the group $G=\{\exp(t_0X_0)\cdots\exp(t_{d-1}X_{d-1})\}$ (closed under products) and the lattice $\Gamma=\{\exp(t_0X_0)\cdots\exp(t_{d-1}X_{d-1}) : t\in\mathbb Z^d\}$, required to be a subgroup, so that the Mal'cev coordinates of the second kind satisfy $\psi(\Gamma)=\mathbb Z^d$.
--
--   The **complexity** is $\max(1,\max_{i,j,k}\mathrm{height}(c_{ijk}))$. The metric on $G$ is that of LSS Definition 3.4, $d(x,y)=\inf\sum_i\min(\|\psi(x_ix_{i+1}^{-1})\|_\infty,\|\psi(x_{i+1}x_i^{-1})\|_\infty)$ over chains $x=x_0,\dots,x_{m+1}=y$ in $G$, and `distQ` is the quotient metric $d(x\Gamma,y\Gamma)=\inf_{\gamma,\gamma'\in\Gamma}d(x\gamma,y\gamma')$. A sequence $g:\mathbb Z\to G$ is **polynomial** (`IsPoly`) if $\partial_{h_1}\cdots\partial_{h_m}g(n)\in G_m$ for all $m$, $h_i$, $n$, where $\partial_hg(n)=g(n+h)g(n)^{-1}$. `IsLip K F` says that $F$ is a right-$\Gamma$-invariant function on $G$ (i.e. a function on $G/\Gamma$) with $|F|\le K$ and Lipschitz constant $\le K$ (implied by $\|F\|_{\mathrm{Lip}}\le K$). Finally `NilStr s N Q φ` says that $\varphi$ is the real or imaginary part of a nilsequence $F(g(n)\Gamma)$ of degree $s$ with dimension $\le 1+\log Q$, complexity $\le Q$ and `IsLip Q F`.
-- source:
--   J. Leng, A. Sah, M. Sawhney, Quasipolynomial bounds for the inverse theorem for the Gowers U^{s+1}[N]-norm, arXiv:2402.17994, Sections 2–3 (Definitions 2.3–2.7, 3.1–3.5); B. Green, T. Tao, The quantitative behaviour of polynomial orbits on nilmanifolds, Ann. of Math. 175 (2012), Section 2

import Mathlib
import Definitions.Def_LSSInterface



/-!
# Nilmanifolds, polynomial sequences and Lipschitz functions (Green–Tao / Leng–Sah–Sawhney)

We formalise the objects appearing in the inverse theorem for the Gowers norms, following
Definitions 2.3–2.7 and 3.1–3.5 of Leng–Sah–Sawhney (arXiv:2402.17994), which are those of
Green–Tao, *The quantitative behaviour of polynomial orbits on nilmanifolds*.

Every connected, simply connected nilpotent Lie group is isomorphic to a closed subgroup of
the group of unipotent upper triangular real matrices (Ado–Birkhoff), with Lie algebra a Lie
algebra of strictly upper triangular matrices; the exponential map is then the (finite) matrix
exponential.  We therefore present a nilmanifold `G/Γ` of degree `s`, dimension `d` and
complexity `≤ M` by

* a Mal'cev basis `X_0, …, X_{d-1}` of `log G`, consisting of strictly upper triangular
  `n × n` real matrices, with rational structure constants `[X_i, X_j] = ∑_k c_{ijk} X_k`
  whose heights are the complexity;
* the Mal'cev ideal property: `span(X_j, …, X_{d-1})` is an ideal for every `j`, i.e.
  `c_{ijk} ≠ 0 → max i j ≤ k`;
* a degree `s` filtration `G = G_0 = G_1 ⊇ G_2 ⊇ ⋯ ⊇ G_{s+1} = {id}` adapted to the basis:
  `log G_i = span(X_j : d - dim G_i ≤ j)`, with `[log G_i, log G_j] ⊆ log G_{i+j}`;
* the lattice `Γ = {exp(t_0 X_0) ⋯ exp(t_{d-1} X_{d-1}) : t ∈ ℤ^d}`, which is required to be a
  subgroup (so that `ψ_X(Γ) = ℤ^d` for the Mal'cev coordinates `ψ_X` of the second kind).

The metric on `G` is that of Definition 3.4 of Leng–Sah–Sawhney, and the metric on `G/Γ` is the
induced quotient metric.  A function on `G/Γ` is represented by a right `Γ`-invariant function
on `G`.
-/

open Finset Matrix

namespace LSS

noncomputable section

/-- Height of a rational number: `max(|a|, b)` for `a/b` in lowest terms. -/
def ratHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- The matrix exponential `∑_{k ≤ n} A^k / k!`; for a strictly upper triangular `n × n` matrix
this is the exponential series (which terminates). -/
def mexp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k ∈ range (n + 1), ((Nat.factorial k : ℝ)⁻¹) • A ^ k

/-- A nilmanifold of degree `s`, presented by an adapted Mal'cev basis of strictly upper
triangular matrices (see the module docstring). -/
structure Nilmanifold (s : ℕ) where
  /-- size of the matrices realising `G` -/
  n : ℕ
  /-- the dimension of `G` -/
  d : ℕ
  /-- the Mal'cev basis of `log G` -/
  X : Fin d → Matrix (Fin n) (Fin n) ℝ
  strictUpper : ∀ i (a b : Fin n), b ≤ a → X i a b = 0
  linIndep : LinearIndependent ℝ X
  /-- structure constants -/
  c : Fin d → Fin d → Fin d → ℚ
  bracket : ∀ i j, X i * X j - X j * X i = ∑ k, ((c i j k : ℚ) : ℝ) • X k
  /-- Mal'cev (ideal) property of the basis -/
  ideal : ∀ i j k, c i j k ≠ 0 → i ≤ k ∧ j ≤ k
  /-- `dimG i = dim G_i` -/
  dimG : ℕ → ℕ
  dimG_zero : dimG 0 = d
  dimG_one : dimG 1 = d
  dimG_anti : Antitone dimG
  dimG_top : dimG (s + 1) = 0
  /-- the filtration property `[log G_i, log G_j] ⊆ log G_{i+j}` on basis elements -/
  filt : ∀ (i j : ℕ) (a b : Fin d), d - dimG i ≤ a.val → d - dimG j ≤ b.val →
    ∀ k, c a b k ≠ 0 → d - dimG (i + j) ≤ k.val
  /-- `G` (the image of the Mal'cev coordinate map) is closed under multiplication -/
  group_mul : ∀ t u : Fin d → ℝ, ∃ v : Fin d → ℝ,
    (List.ofFn fun k => mexp (t k • X k)).prod * (List.ofFn fun k => mexp (u k • X k)).prod =
    (List.ofFn fun k => mexp (v k • X k)).prod
  /-- `Γ` is closed under multiplication -/
  lattice_mul : ∀ t u : Fin d → ℤ, ∃ v : Fin d → ℤ,
    (List.ofFn fun k => mexp (((t k : ℤ) : ℝ) • X k)).prod *
      (List.ofFn fun k => mexp (((u k : ℤ) : ℝ) • X k)).prod =
    (List.ofFn fun k => mexp (((v k : ℤ) : ℝ) • X k)).prod
  /-- `Γ` is closed under inversion -/
  lattice_inv : ∀ t : Fin d → ℤ, ∃ v : Fin d → ℤ,
    (List.ofFn fun k => mexp (((t k : ℤ) : ℝ) • X k)).prod *
      (List.ofFn fun k => mexp (((v k : ℤ) : ℝ) • X k)).prod = 1

namespace Nilmanifold

variable {s : ℕ} (G : Nilmanifold s)

/-- The matrix type in which `G` is realised. -/
abbrev Mat : Type := Matrix (Fin G.n) (Fin G.n) ℝ

/-- The element `exp(t_0 X_0) ⋯ exp(t_{d-1} X_{d-1})` with Mal'cev coordinates (of the second
kind) `t`. -/
def malcev (t : Fin G.d → ℝ) : G.Mat := (List.ofFn fun k => mexp (t k • G.X k)).prod

/-- Membership in the group `G`. -/
def Mem (x : G.Mat) : Prop := ∃ t, G.malcev t = x

/-- Membership in the filtration subgroup `G_i`. -/
def MemFil (i : ℕ) (x : G.Mat) : Prop :=
  ∃ t : Fin G.d → ℝ, (∀ k : Fin G.d, k.val < G.d - G.dimG i → t k = 0) ∧ G.malcev t = x

/-- Membership in the lattice `Γ`. -/
def MemΓ (x : G.Mat) : Prop := ∃ t : Fin G.d → ℤ, G.malcev (fun k => (t k : ℝ)) = x

/-- The complexity of the nilmanifold: the largest height of a structure constant (at least `1`). -/
def complexity : ℝ := max 1 (⨆ ijk : Fin G.d × Fin G.d × Fin G.d,
  (ratHeight (G.c ijk.1 ijk.2.1 ijk.2.2) : ℝ))

/-- `‖ψ(x)‖_∞`, the sup norm of the Mal'cev coordinates of `x ∈ G`. -/
def coordNorm (x : G.Mat) : ℝ := sInf {r | ∃ t : Fin G.d → ℝ, G.malcev t = x ∧ r = ‖t‖}

/-- The metric on `G` (Definition 3.4 of Leng–Sah–Sawhney):
`d(x, y) = inf ∑_i min(‖ψ(x_i x_{i+1}⁻¹)‖, ‖ψ(x_{i+1} x_i⁻¹)‖)` over chains
`x = x_0, x_1, …, x_{m+1} = y` in `G`. -/
def dist (x y : G.Mat) : ℝ :=
  sInf {r | ∃ (m : ℕ) (z : Fin (m + 2) → G.Mat), z 0 = x ∧ z (Fin.last (m + 1)) = y ∧
    (∀ i, G.Mem (z i)) ∧
    r = ∑ i : Fin (m + 1), min (G.coordNorm (z i.castSucc * (z i.succ)⁻¹))
      (G.coordNorm (z i.succ * (z i.castSucc)⁻¹))}

/-- The quotient metric on `G/Γ`: `d(xΓ, yΓ) = inf_{γ, γ' ∈ Γ} d(xγ, yγ')`. -/
def distQ (x y : G.Mat) : ℝ :=
  sInf {r | ∃ γ γ' : G.Mat, G.MemΓ γ ∧ G.MemΓ γ' ∧ r = G.dist (x * γ) (y * γ')}

/-- The derivative `∂_h g(n) = g(n + h) g(n)⁻¹`. -/
def deriv (h : ℤ) (g : ℤ → G.Mat) : ℤ → G.Mat := fun m => g (m + h) * (g m)⁻¹

/-- Iterated derivatives `∂_{h_1} ⋯ ∂_{h_m} g`. -/
def derivs (hs : List ℤ) (g : ℤ → G.Mat) : ℤ → G.Mat := hs.foldr G.deriv g

/-- `g : ℤ → G` is a polynomial sequence with respect to the degree `s` filtration
(Definition 2.5 of Leng–Sah–Sawhney, domain `ℤ` with its degree filtration): every
`m`-fold derivative takes values in `G_m`. -/
def IsPoly (g : ℤ → G.Mat) : Prop :=
  (∀ m, G.Mem (g m)) ∧ ∀ (hs : List ℤ) (m : ℤ), G.MemFil hs.length (G.derivs hs g m)

/-- `F` is a function on `G/Γ` (a right `Γ`-invariant function on `G`) with `‖F‖_∞ ≤ K` and
Lipschitz constant `≤ K`; this is implied by `‖F‖_{Lip} ≤ K` and implies `‖F‖_{Lip} ≤ 2K`. -/
def IsLip (K : ℝ) (F : G.Mat → ℂ) : Prop :=
  (∀ x γ, G.Mem x → G.MemΓ γ → F (x * γ) = F x) ∧ (∀ x, G.Mem x → ‖F x‖ ≤ K) ∧
    ∀ x y, G.Mem x → G.Mem y → ‖F x - F y‖ ≤ K * G.dist x y

end Nilmanifold

/-- The class of (real and imaginary parts of) Lipschitz nilsequences of degree `s`, with
dimension at most `1 + log Q` and complexity and Lipschitz norm at most `Q`. -/
def NilStr (s : ℕ) (_N : ℕ) (Q : ℝ) (φ : ℤ → ℝ) : Prop :=
  ∃ (G : Nilmanifold s) (g : ℤ → G.Mat) (F : G.Mat → ℂ),
    (G.d : ℝ) ≤ 1 + Real.log Q ∧ G.complexity ≤ Q ∧ G.IsPoly g ∧ G.IsLip Q F ∧
    ((∀ m, φ m = (F (g m)).re) ∨ (∀ m, φ m = (F (g m)).im))

end

end LSS


