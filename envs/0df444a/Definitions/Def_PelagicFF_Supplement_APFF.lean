-- Prove2me | Definitions.Def_PelagicFF_Supplement_APFF
-- name    : PelagicFF_Supplement_APFF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:26:11.530862+00:00
-- url     : https://prove2.me/theorems/ef2bfa14-12e9-424c-ae83-cfa2ea24ad1d
-- title:
--   Affine Pelagic Fourier Fishing $\mathrm{APFF}_n$ (Problem 5.1)
-- statement:
--   Let $n\ge4$, $N=2^n$, $\ell=\lceil 2\log_2 n\rceil$ and $K=2^\ell$, so that $\ell\le n$ and $n^2\le K<2n^2$. Identify $\{0,1\}^n$ with $\mathbb F_2^n$.
--
--   Alice receives a function $f:\{0,1\}^n\to\{-1,1\}$ (a truth table of length $N$). Bob receives an $\ell$-dimensional linear subspace $V\le\mathbb F_2^n$, specified by a publicly fixed basis $b_1(V),\dots,b_\ell(V)$. Bob outputs $a\in\{0,1\}^n$, specifying the coset $U=V+a$, and $y\in\{0,1\}^\ell$, identified with the linear functional on $V$ sending $b_i\mapsto y_i$. With
--
--   $$
--   \widehat f_U(y)=\frac1{|V|}\sum_{v\in V}f(a+v)\chi_y(v)=\frac1K\sum_{c\in\{0,1\}^\ell}f\Big(a+\sum_i c_ib_i\Big)(-1)^{c\cdot y},
--   $$
--
--   the output $(a,y)$ is correct when
--
--   $$
--   \sum_{z:\ |\widehat f_U(z)|\le|\widehat f_U(y)|}|\widehat f_U(z)|^2\ge\frac18,\qquad \sum_{z:\ |\widehat f_U(z)|\ge|\widehat f_U(y)|}|\widehat f_U(z)|^2\ge\frac18,\tag{14}
--   $$
--
--   the sums ranging over $z\in V^*\cong\{0,1\}^\ell$.
--
--   This is the problem of Theorem 5.2, which separates $n$ qubits from $\Theta(2^n)$ bits of randomized one-way communication while keeping answers efficiently verifiable.
--
--   **Formalization Note** $\ell$ is `Nat.clog 2 (n^2)`, which equals $\lceil 2\log_2 n\rceil$ for $n\ge1$. Subspaces are `Submodule (ZMod 2) (Fin n → ZMod 2)` of `finrank` $\ell$. The paper does not name its canonical basis, so the relation takes a basis choice `bas` (a basis of every $\ell$-dimensional subspace) as a parameter. Condition (14) is the published Pelagic condition `PelagicFF.IsPelagic` (eq. (9)) of $c\mapsto f(a+\sum_i c_ib_i)$ at $y$; $f$ is `Bool`-valued, read through $\mathrm{false}\mapsto1$, $\mathrm{true}\mapsto-1$.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 5.1, eq. (14), p.32; §2.2, p.14 (coset Fourier coefficient); §5.1, p.33 (the formula in the basis)

import Mathlib
import Definitions.Def_PelagicFF_PFF

open OAI.Cotype

namespace PelagicFF.Supplement

/-- `ℓ = ⌈2 log₂ n⌉`, computed as `Nat.clog 2 (n²)`, the least `k` with `n² ≤ 2^k`; the coset size
is `K = 2^ℓ`. arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 5.1, p.32: "for n ≥ 4,
set ℓ = ⌈2 log₂ n⌉ and K = 2^ℓ, so that ℓ ≤ n and n² ≤ K < 2n²".

**Formalization Note.** For `n ≥ 1`, `⌈2 log₂ n⌉ = ⌈log₂ n²⌉ = Nat.clog 2 (n²)`. -/
def ell (n : ℕ) : ℕ := Nat.clog 2 (n ^ 2)

/-- The `ℓ`-dimensional linear subspaces `V ≤ F₂ⁿ` (Bob's inputs in `APFFₙ`). -/
abbrev Grass (n k : ℕ) : Type :=
  {V : Submodule (ZMod 2) (Fin n → ZMod 2) // Module.finrank (ZMod 2) V = k}

/-- There are finitely many subspaces of `F₂ⁿ` (needed for the uniform law on Bob's input). -/
noncomputable instance (n k : ℕ) : Fintype (Grass n k) := Fintype.ofFinite _

/-- A vector of `F₂ⁿ` read as a point of `{0,1}ⁿ` (the coordinate `1 ∈ ZMod 2` is `true`). -/
def toBits {n : ℕ} (v : Fin n → ZMod 2) : Fin n → Bool := fun i => decide (v i = 1)

/-- A choice of basis `b₁(V), …, b_ℓ(V)` for every `ℓ`-dimensional subspace `V ≤ F₂ⁿ` (the paper's
"publicly fixed canonical basis", which the paper does not name). -/
abbrev BasisChoice (n : ℕ) : Type :=
  ∀ V : Grass n (ell n), Module.Basis (Fin (ell n)) (ZMod 2) V.1

/-- Bob's output in `APFFₙ`: a coset representative `a ∈ F₂ⁿ` and `y ∈ {0,1}^ℓ`. -/
abbrev APFFOut (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin (ell n) → Bool)

/-- The point `a + ∑_{i : cᵢ = 1} bᵢ(V)` of the coset `U = V + a`, for `c ∈ {0,1}^ℓ`. -/
noncomputable def cosetPoint {n : ℕ} (bas : BasisChoice n) (V : Grass n (ell n)) (a : Fin n → ZMod 2)
    (c : Fin (ell n) → Bool) : Fin n → ZMod 2 :=
  a + ∑ i, if c i then ((bas V i : V.1) : Fin n → ZMod 2) else 0

/-- **Affine Pelagic Fourier Fishing `APFFₙ` (Problem 5.1)** as a two-party search relation, for
the basis choice `bas`. Alice holds `f : {0,1}ⁿ → {−1,1}`, Bob holds an `ℓ`-dimensional subspace
`V ≤ F₂ⁿ`; the output `(a, y)` is correct exactly when (14) holds for the coset `U = V + a`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 5.1, p.32: "Bob must output a string
a ∈ {0,1}ⁿ, specifying a coset U = V + a, and a string y ∈ {0,1}^ℓ, identified with the linear map
in V* sending bᵢ ↦ yᵢ. The output is correct if
∑_{z∈V*: |f̂_U(z)| ≤ |f̂_U(y)|} |f̂_U(z)|² ≥ 1/8, ∑_{z∈V*: |f̂_U(z)| ≥ |f̂_U(y)|} |f̂_U(z)|² ≥ 1/8 (14)",
with `f̂_U(y) = (1/|V|) ∑_{v∈V} f(a + v) χ_y(v)` (§2.2, p.14).

**Formalization Note.** Through the basis, `V*` is `{0,1}^ℓ` and, as on p.33,
`f̂_U(y) = (1/K) ∑_{c∈{0,1}^ℓ} f(a + ∑ cᵢbᵢ)(−1)^{c·y}`, the Fourier coefficient at `y` of
`c ↦ f(a + ∑ cᵢbᵢ)` on `{0,1}^ℓ`. So (14) is the published Pelagic condition `IsPelagic` (eq. (9))
of that function at `y`. The `{−1,1}` value of `f` is `OAI.Cotype.sign` of its bit. -/
noncomputable def APFF {n : ℕ} (bas : BasisChoice n) (f : PelagicFF.BoolFn n) (V : Grass n (ell n))
    (o : APFFOut n) : Prop :=
  PelagicFF.IsPelagic (fun c => sign (f (toBits (cosetPoint bas V o.1 c)))) o.2

end PelagicFF.Supplement


