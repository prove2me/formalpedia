-- Prove2me | Definitions.Def_IntConeFPT_Residue
-- name    : IntConeFPT_Residue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:05.979231+00:00
-- url     : https://prove2.me/theorems/296fb52a-8be8-4bee-a592-bbfccf1ef31a
-- title:
--   Residue classes $S_r^{(t)}$, residue hulls $P_r^{(t)}$, fiber vertices $V_r^{(t)}$, the cone $C_r^{(t)}$, the fractional cost $\Phi_r^{(t)}$ (3.1a) and its dual region $D_r^{(t)}$ (3.1b)
-- statement:
--   For a residue vector $r\in\{0,\dots,2^d-1\}^d$ and a type $t$:
--   $$
--   S^{(t)}_r=P^{(t)}\cap\big((r+2^d\mathbb Z^d)\times\mathbb R^k\big),\qquad P^{(t)}_r=\operatorname{conv}(S^{(t)}_r).
--   $$
--   The **fiber** of $x\in\mathbb Z^d$ is $\{u\in\mathbb R^k:(x,u)\in P^{(t)}\}$, and $V^{(t)}_r$ consists of the $(x,u)\in S^{(t)}_r$ such that $u$ is a vertex (extreme point) of the fiber of $x$. The **homogenization cone** is
--   $$
--   C^{(t)}_r=\{(0,0,0)\}\cup\{(z,w,n)\in\mathbb R^d\times\mathbb R^k\times\mathbb R_{>0}:(z/n,w/n)\in P^{(t)}_r\}.
--   $$
--   A **fractional representation** of $(z,w,n)$ by a set $T$ of generators is a finitely supported $\theta\ge0$ on $T$ with $\sum\theta_{(x,u)}(x,u)=(z,w)$ and $\sum\theta_{(x,u)}=n$. The **fractional cost** (3.1a) is
--   $$
--   \Phi^{(t)}_r(z,w,n)=\inf\Big\{\sum_{(x,u)\in V^{(t)}_r}\theta_{(x,u)}f^{(t)}(x):\theta\text{ a fractional representation of }(z,w,n)\text{ by }V^{(t)}_r\Big\}\in\mathbb R\cup\{+\infty\},
--   $$
--   equal to $+\infty$ when no representation exists. The **dual region** (3.1b) is $D^{(t)}_r=\{(a,b)\in\mathbb R^{d+k}\times\mathbb R:\langle a,(x,u)\rangle+b\le f^{(t)}(x)\ \forall(x,u)\in V^{(t)}_r\}$.
--
--   For an empty class, $P^{(t)}_r=\emptyset$, so $C^{(t)}_r=\{(0,0,0)\}$ and $\Phi^{(t)}_r(0,0,0)=0$ (the empty representation), as the paper sets on p.8.
--
--   **Formalization Note** $\Phi^{(t)}_r$ takes values in `EReal`. The module also fixes the binary encodings of residue vectors, of a per-type subroutine call $(I,t,r)$, and of the outputs of Lemmas 5, 12 and 29.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3, pp.7–8, (3.1a), (3.1b)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem

namespace IntConeFPT

open OnlineCRS.Combine

/-- **Residue vectors `r ∈ {0, …, 2^d − 1}^d`** (§3, p.7). -/
abbrev Residue (d : ℕ) : Type := Fin d → Fin (2 ^ d)

/-- **Points `(z, w, n) ∈ R^d × R^k × R`** of the homogenization cone (§3, p.8). -/
abbrev Pt (d k : ℕ) : Type := (Fin d → ℝ) × (Fin k → ℝ) × ℝ

/-- **The pairing `⟨a, (x, u)⟩`** on `R^{d+k}`. -/
def pairing {d k : ℕ} (a p : (Fin d → ℝ) × (Fin k → ℝ)) : ℝ :=
  ∑ i, a.1 i * p.1 i + ∑ j, a.2 j * p.2 j

/-- A rational generator `(x, u) ∈ Z^d × Q^k` as a generator with real `u`. -/
def ratGen {d k : ℕ} (x : Fin d → ℤ) (u : Fin k → ℚ) : Gen d k :=
  (x, fun j => (u j : ℝ))

/-- A rational vector `(a_x, a_u) ∈ Q^d × Q^k` as a point of `R^{d+k}`. -/
def ratPair {d k : ℕ} (a : Fin d → ℚ) (b : Fin k → ℚ) : (Fin d → ℝ) × (Fin k → ℝ) :=
  (fun i => (a i : ℝ), fun j => (b j : ℝ))

/-- **Fractional representations** of `(z, w, n)` by generators from `T` (§3, p.8): finitely
supported `θ ≥ 0` on `T` with `Σ θ_(x,u) (x, u) = (z, w)` and `Σ θ_(x,u) = n`. -/
def IsFracRep {d k : ℕ} (T : Set (Gen d k)) (θ : Gen d k →₀ ℝ) (ξ : Pt d k) : Prop :=
  (↑θ.support : Set (Gen d k)) ⊆ T ∧ (∀ g, 0 ≤ θ g) ∧
    (θ.sum fun g c => c • g.toReal) = (ξ.1, ξ.2.1) ∧ (θ.sum fun _ c => c) = ξ.2.2

/-- **The cost `Σ θ_(x,u) f(x)` of a fractional representation** (§3, p.8). -/
def fracCost {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (θ : Gen d k →₀ ℝ) : ℝ :=
  θ.sum fun g c => c * f (fun i => (g.1 i : ℝ))

namespace Instance

/-- **The residue class `S_r^(t) := P^(t) ∩ ((r + 2^d Z^d) × R^k)`**.
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §3, p.7. -/
def Sr (I : Instance) (t : Fin I.τ) (r : Residue I.d) : Set (Gen I.d I.k) :=
  {g | g ∈ I.S t ∧ ∀ i, g.1 i ≡ ((r i : ℕ) : ℤ) [ZMOD 2 ^ I.d]}

/-- **The residue hull `P_r^(t) := conv(S_r^(t))`** (§3, p.7), in `R^{d+k}`. It may contain
integer points of other residues. -/
def Pr (I : Instance) (t : Fin I.τ) (r : Residue I.d) : Set ((Fin I.d → ℝ) × (Fin I.k → ℝ)) :=
  convexHull ℝ (Gen.toReal '' I.Sr t r)

/-- **The fiber of `x`**: `{u ∈ R^k : (x, u) ∈ P^(t)}` (§3, p.8). -/
def fiber (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) : Set (Fin I.k → ℝ) :=
  {u | ((fun i => (x i : ℝ)), u) ∈ I.P t}

/-- **Fiber vertices `V_r^(t)`** (§3, p.8): "all pairs (x, u) in S_r^(t) for which u is a vertex of
its fiber". -/
def Vr (I : Instance) (t : Fin I.τ) (r : Residue I.d) : Set (Gen I.d I.k) :=
  {g | g ∈ I.Sr t r ∧ g.2 ∈ Set.extremePoints ℝ (I.fiber t g.1)}

/-- **The homogenization cone `C_r^(t) ⊆ R^{d+k+1}`** (§3, p.8):
`C_r^(t) := {(0, 0, 0)} ∪ {(z, w, n) ∈ R^d × R^k × R_{>0} : (z/n, w/n) ∈ P_r^(t)}`.
For an empty class `P_r^(t) = ∅`, so `C_r^(t) = {(0, 0, 0)}`, as the paper sets. -/
def Cr (I : Instance) (t : Fin I.τ) (r : Residue I.d) : Set (Pt I.d I.k) :=
  {0} ∪ {ξ | 0 < ξ.2.2 ∧ (ξ.2.2⁻¹ • ξ.1, ξ.2.2⁻¹ • ξ.2.1) ∈ I.Pr t r}

/-- **The fractional cost `Φ_r^(t)`, (3.1a)** (§3, p.8):
`Φ_r^(t)(z, w, n) := min { Σ_{(x,u)∈V_r} θ_(x,u) f^(t)(x) : θ ≥ 0, Σ θ_(x,u) (x, u) = (z, w),
Σ θ_(x,u) = n }`, with value `+∞` when no such `θ` exists.

**Formalization Note.** The value lies in `EReal`: it is the infimum over the fractional
representations by fiber vertices, and `⊤` when there is none (outside `C_r^(t)`). At `(0, 0, 0)`
the only representation is `θ = 0`, so `Φ_r^(t)(0, 0, 0) = 0`, also for an empty class (p.8). -/
noncomputable def Phi (I : Instance) (t : Fin I.τ) (r : Residue I.d) (ξ : Pt I.d I.k) : EReal :=
  ⨅ θ ∈ {θ | IsFracRep (I.Vr t r) θ ξ}, ((fracCost (I.f t) θ : ℝ) : EReal)

/-- **The dual feasible region `D_r^(t)` of (3.1b)** (§3, p.8): all `(a, b) ∈ R^{d+k} × R` with
`⟨a, (x, u)⟩ + b ≤ f^(t)(x)` for every `(x, u) ∈ V_r^(t)`. -/
def Dr (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    Set (((Fin I.d → ℝ) × (Fin I.k → ℝ)) × ℝ) :=
  {ab | ∀ g ∈ I.Vr t r, pairing ab.1 g.toReal + ab.2 ≤ I.f t (fun i => (g.1 i : ℝ))}

end Instance

/-- Binary encoding of a residue vector: each entry by `encNat`, followed by `3`. -/
def encResidue {d : ℕ} (r : Residue d) : List Sym :=
  (List.finRange d).flatMap fun i => encNat (r i) ++ [3]

/-- **Encoding of a per-type subroutine call `(I, t, r)`** (B.1, p.33: "Fix a type t"):
the instance, then `t` in binary, then the residue vector. A query is appended to it. -/
def encLocal (I : Instance) (t : Fin I.τ) (r : Residue I.d) : List Sym :=
  encInstance I ++ encNat t ++ [3] ++ encResidue r

/-- Binary encoding of a rational generator `(x, u) ∈ Z^d × Q^k`. -/
def encGen {d k : ℕ} (x : Fin d → ℤ) (u : Fin k → ℚ) : List Sym :=
  encIntVec x ++ encVec u

/-- Encoding of the output of Lemma 29: `0` (empty class) or `1` and a rational generator. -/
def encPricing {d k : ℕ} : Option ((Fin d → ℤ) × (Fin k → ℚ)) → List Sym
  | none => [0]
  | some g => [1] ++ encGen g.1 g.2

/-- Encoding of the output of Lemma 12: `0` (member) or `1`, a rational normal `c ∈ Q^{d+k}` and
a rational `β`. -/
def encSeparation {d k : ℕ} : Option (((Fin d → ℚ) × (Fin k → ℚ)) × ℚ) → List Sym
  | none => [0]
  | some cb => [1] ++ encVec cb.1.1 ++ encVec cb.1.2 ++ encRat cb.2 ++ [3]

/-- Encoding of the output of Lemma 5: the value `Φ`, the dual pair `(a⋆, b⋆)`, and the
fractional representation as entries `(x, u, θ)` with rational `u` and `θ`. -/
def encOracle {d k : ℕ}
    (o : ℚ × ((Fin d → ℚ) × (Fin k → ℚ)) × ℚ × List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    List Sym :=
  encRat o.1 ++ [3] ++ encVec o.2.1.1 ++ encVec o.2.1.2 ++ encRat o.2.2.1 ++ [3] ++
    encNat o.2.2.2.length ++ [3] ++
    o.2.2.2.flatMap fun e => encGen e.1 e.2.1 ++ encRat e.2.2 ++ [3]

end IntConeFPT


