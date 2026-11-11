-- Prove2me | Definitions.Def_SingleExpBisect_Main_NodeData
-- name    : SingleExpBisect_Main_NodeData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:39:44.933952+00:00
-- url     : https://prove2.me/theorems/f3055107-3431-4bb7-859b-8870bbcef020
-- title:
--   Node data of the dynamic program: µ_t, η_t, Φ_t, Z_t, Z_t^{≤2k}, Q_{t,R}, ω_t^X, boundary coefficients, Laurent embedding, L_{t,S}
-- statement:
--   Fix a graph $G$ on $\{0,\dots,n-1\}$, a vertex set $W$ (playing $V(G_t)$), and for nodes of a rooted tree decomposition $T$: $V(G_t)$ is the union of the bags in the subtree of $t$ (published `T.cone t`), $\partial G_t=B_t\cap B_{t'}$ for the parent $t'$ and $\emptyset$ at the root (published `T.adhesion t`), and $G_t[B_t]$ is the published `bagGraph`. The variables are $y_v$ ($v$ a vertex), $x$, $x'$ and $w$.
--
--   - $\mu_t(A_t)=\min\{|\delta_G(A)|: A\subseteq V(G),\ A\cap W=A_t\}$ (minimum completion cost, cut in all of $G$).
--   - $\eta_t(P)=\min\{|\delta_{G-(V(G_t)\setminus\partial G_t)}(A)| : A\subseteq V(G)\setminus(V(G_t)\setminus\partial G_t),\ A\cap\partial G_t=P\}$.
--   - $\Phi_t(S)$: the union of all $A\subseteq V(G)$ with $A\cap W=S$ and $|\delta_G(A)|=\mu_t(S)$ (the largest such set when one exists, Lemma 3.7).
--   - $Z_t(y,w)=\sum_{A_t\subseteq W,\ \mu_t(A_t)\le k} w^{\mu_t(A_t)}\prod_{v\in A_t}y_v$; $Z_t^{\le2k}$ adds $|A_t\cap B_t|\le2k$; $Q_{t,R}(x,w)=\sum_{A_t\subseteq W,\ \mu_t(A_t)\le k,\ A_t\cap B_t=R} x^{|A_t\setminus B_t|}w^{\mu_t(A_t)}$.
--   - $\omega^X$ substitutes $y_v\mapsto y_v$ for $v\in X$ and $y_v\mapsto x$ otherwise; `Zomega G T k t` is $Z_t(\omega^{\partial G_t}_t(y,x),w)$.
--   - $[\prod_{v\in P}y_v]_y F$: the terms of $F$ whose $y$-part is exactly $\prod_{v\in P}y_v$, with that part removed.
--   - Laurent polynomials $\mathbb Q[\text{variables}^{\pm1}]$ (`AddMonoidAlgebra ℚ (Var n →₀ ℤ)`): `toL` embeds polynomials, `wPow z` is $w^z$ ($z\in\mathbb Z$), `truncWL k` is $\langle\cdot\rangle_{\deg_w\le k}$, `invY` is $y\mapsto y^{-1}$, `yProdL W` is $\prod_{v\in W}y_v$.
--   - The $B_t$-support of a monomial $x^bw^\ell\prod y_v^{a_v}$ is $\{v\in B_t: a_v>0\}$; $L_{t,S}$ is the part of $\log Z_t^{\le2k}(y,w)$ with $B_t$-support $S$; $\langle\cdot\rangle_{\le(k,n,2k)}$ keeps $\deg_w\le k$, $\deg_x\le n$, $\sum_{v\in B_t}\deg_{y_v}\le2k$.
--
--   **Formalization Note.** Minima are `sInf` over $\mathbb N$ of sets that are nonempty whenever the argument lies in its range ($A_t\subseteq W$, $P\subseteq\partial G_t$), which is the only way they are used. No object is defined through a recurrence it satisfies.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.1, p. 15 (G_t, ∂G_t, µ_t, Z_t, ω); §3.2, pp. 17–18 (Q_{t,R}, (5), η_t, (8), Z^{≤2k}); p. 19 (y^{−1}); §3.3, p. 20 (B_t-support, L_{t,S}, ⟨·⟩_{≤(k,n,2k)}); §3.4, p. 24 (Φ_t); §2, p. 14 ([m]_u F)

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_MinBisectFPT_RootedTD
import Definitions.Def_SingleExpBisect_Main_FormalSeries

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- **The variables of Section 3.** Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection
and Matching Cut via a New Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3,
pp. 15–22: a vertex variable `y_v` for every vertex `v`, the size variable `x`, the fresh variable
`x′` of §3.3 (p. 22), and the cut variable `w`. -/
inductive Var (n : ℕ) where
  | y (v : Fin n)
  | x
  | x'
  | w
  deriving DecidableEq, Fintype

/-- `z` is a vertex variable `y_v`. -/
def IsYVar {n : ℕ} (z : Var n) : Prop := ∃ v, z = Var.y v

/-- **Minimum completion cost.** ibid., §3.1, p. 15: "For A_t ⊆ V(G_t), define the minimum
completion cost of A_t by µ_t(A_t) := min{|δ_G(A)| : A ∩ V(G_t) = A_t}."

**Formalization Note.** `W` plays `V(G_t)`; the minimum is over all `A ⊆ V(G)` (`Finset (Fin n)`),
cut in the whole graph `G` (published `cutSize`). For `S ⊆ W` the set is nonempty (`A = S`), so the
`sInf` over `ℕ` is the minimum; every use has `S ⊆ W`. -/
noncomputable def mu {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) : ℕ :=
  sInf {c : ℕ | ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = c}

/-- **The boundary correction η_t.** ibid., §3.2, p. 17: "For P ⊆ ∂G_t, define
η_t(P) := min{|δ_{G−(V(G_t)\∂G_t)}(A)| : A ⊆ V(G) \ (V(G_t) \ ∂G_t), A ∩ ∂G_t = P}."

**Formalization Note.** `W` plays `V(G_t)` and `D` plays `∂G_t`. The graph `G − U` (`U` deleted) is
the published `restrictMinus G (V \ U) ∅` on the ambient type (the vertices of `U` become
isolated). For `P ⊆ D ⊆ W` the set is nonempty (`A = P`). -/
noncomputable def eta {n : ℕ} (G : SimpleGraph (Fin n)) (W D P : Finset (Fin n)) : ℕ :=
  sInf {c : ℕ | ∃ A : Finset (Fin n), A ⊆ Finset.univ \ (W \ D) ∧ A ∩ D = P ∧
    cutSize (restrictMinus G (Finset.univ \ (W \ D)) ∅) A = c}

/-- **Φ_t(S).** ibid., §3.4, p. 24: "for each S ⊆ V(G_t), let Φ_t(S) be the inclusion-wise largest
member of {A ⊆ V(G) : A ∩ V(G_t) = S, |δ_G(A)| = µ_t(S)}."

**Formalization Note.** Defined as the union of all members of that family; when the family has a
largest member (Lemma 3.7) the union is that member. `W` plays `V(G_t)`. -/
noncomputable def Phi {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) : Finset (Fin n) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun A => A ∩ W = S ∧ cutSize G A = mu G W S)).sup id

/-- The exponent vector of `Π_{v ∈ A} y_v`. -/
noncomputable def yMono {n : ℕ} (A : Finset (Fin n)) : Var n →₀ ℕ :=
  ∑ v ∈ A, Finsupp.single (Var.y v) 1

/-- **Z_t.** ibid., §3.1, p. 15: "Z_t(y, w) := Σ_{A_t ⊆ V(G_t), µ_t(A_t) ≤ k} w^{µ_t(A_t)} ·
Π_{v ∈ A_t} y_v." `W` plays `V(G_t)`. -/
noncomputable def Zfull {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (k : ℕ) :
    MvPolynomial (Var n) ℚ :=
  ∑ A ∈ W.powerset.filter (fun A => mu G W A ≤ k),
    MvPolynomial.monomial (Finsupp.single Var.w (mu G W A) + yMono A) 1

/-- **Z_t^{≤2k}.** ibid., §3.2, p. 18: "Z_t^{≤2k}(y, w) := Σ_{A_t ⊆ V(G_t), µ_t(A_t) ≤ k,
|A_t ∩ B_t| ≤ 2k} w^{µ_t(A_t)} · Π_{v ∈ A_t} y_v." `W` plays `V(G_t)`, `B` plays `B_t`. -/
noncomputable def Zle {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (k : ℕ) :
    MvPolynomial (Var n) ℚ :=
  ∑ A ∈ W.powerset.filter (fun A => mu G W A ≤ k ∧ (A ∩ B).card ≤ 2 * k),
    MvPolynomial.monomial (Finsupp.single Var.w (mu G W A) + yMono A) 1

/-- **Q_{t,R}.** ibid., §3.2, p. 17, (5): "Q_{t,R}(x, w) := Σ_{A_t ⊆ V(G_t), µ_t(A_t) ≤ k,
A_t ∩ B_t = R} x^{|A_t \ B_t|} · w^{µ_t(A_t)}." `W` plays `V(G_t)`, `B` plays `B_t`. -/
noncomputable def Qpoly {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (k : ℕ)
    (R : Finset (Fin n)) : MvPolynomial (Var n) ℚ :=
  ∑ A ∈ W.powerset.filter (fun A => mu G W A ≤ k ∧ A ∩ B = R),
    MvPolynomial.monomial (Finsupp.single Var.x (A \ B).card + Finsupp.single Var.w (mu G W A)) 1

/-- The variable map of `ω^X`: `y_v ↦ y_v` for `v ∈ X`, `y_v ↦ x` otherwise; `x, x′, w` fixed. -/
def omegaVar {n : ℕ} (X : Finset (Fin n)) : Var n → Var n
  | Var.y v => if v ∈ X then Var.y v else Var.x
  | z => z

/-- **The substitution ω_t^X.** ibid., §3.1, p. 15: "For X ⊆ V(G_t), define the substitution
ω_t^X(y, x) := (ω^X_{t,v})_{v ∈ V(G_t)}, where ω^X_{t,v} := y_v for v ∈ X and x for
v ∈ V(G_t) \ X." `omega X F` is `F(ω^X(y, x), w)`. (The polynomials it is applied to contain only
`y_v` with `v ∈ V(G_t)`, so its action on other vertex variables is irrelevant.) -/
noncomputable def omega {n : ℕ} (X : Finset (Fin n)) :
    MvPolynomial (Var n) ℚ →ₐ[ℚ] MvPolynomial (Var n) ℚ :=
  MvPolynomial.rename (omegaVar X)

/-- **Boundary-monomial coefficient `[Π_{v ∈ P} y_v]_y F`.** ibid., §2, p. 14: "For u ⊆ X, every
F ∈ Q[[X]] has a unique expansion F = Σ_m F_m m, where m ranges over the monomials in u and
F_m ∈ Q[[X \ u]]; define [m]_u F := F_m." Here `u` is the set of vertex variables and `m` is
`Π_{v ∈ P} y_v`: the terms of `F` whose `y`-part is exactly `Π_{v ∈ P} y_v`, with that part
removed. -/
noncomputable def yCoeff {n : ℕ} (P : Finset (Fin n)) (F : MvPolynomial (Var n) ℚ) :
    MvPolynomial (Var n) ℚ :=
  ∑ e ∈ F.support,
    if (∀ v : Fin n, e (Var.y v) = if v ∈ P then 1 else 0) then
      MvPolynomial.monomial (e.filter (fun z => ¬ IsYVar z)) (MvPolynomial.coeff e F)
    else 0

/-- `Z_t(ω^{∂G_t}_t(y, x), w)` at node `t` of a rooted decomposition `T` of `G`
(ibid., §3.1, p. 16): `V(G_t)` is the published cone of `t` (the union of the bags below `t`), and
`∂G_t` is the published `T.adhesion t` (`B_t ∩ B_{t′}`, and `∅` at the root). -/
noncomputable def Zomega {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ)
    (t : Fin T.N) : MvPolynomial (Var n) ℚ :=
  omega (T.adhesion t) (Zfull G (T.cone t) k)

/-- `η_t` at node `t` of `T`: `eta` with `V(G_t) =` the cone of `t` and `∂G_t = T.adhesion t`. -/
noncomputable def etaNode {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (t : Fin T.N)
    (P : Finset (Fin n)) : ℕ :=
  eta G (T.cone t) (T.adhesion t) P

/-- **Laurent polynomials in the variables of Section 3** (exponents in `ℤ`), used for the factors
`w^{−η_s(·)}` of (8) (p. 17) and `y^{−1}` of Lemma 3.2 (p. 19). -/
abbrev LPoly (n : ℕ) : Type := AddMonoidAlgebra ℚ (Var n →₀ ℤ)

/-- A polynomial viewed as a Laurent polynomial (the same monomials and coefficients). -/
noncomputable def toL {n : ℕ} (F : MvPolynomial (Var n) ℚ) : LPoly n :=
  AddMonoidAlgebra.mapDomain (Finsupp.mapRange (fun a : ℕ => (a : ℤ)) Nat.cast_zero) F

/-- The Laurent monomial `w^z`, `z ∈ ℤ`. -/
noncomputable def wPow {n : ℕ} (z : ℤ) : LPoly n :=
  AddMonoidAlgebra.single (Finsupp.single Var.w z) 1

/-- `⟨F⟩_{deg_w ≤ k}` on Laurent polynomials: the monomials of `w`-degree `> k` are discarded
(ibid., (8), p. 17). -/
noncomputable def truncWL {n : ℕ} (k : ℕ) (F : LPoly n) : LPoly n :=
  AddMonoidAlgebra.ofCoeff (F.coeff.filter (fun e => e Var.w ≤ (k : ℤ)))

/-- **The substitution `y ↦ y^{−1}`** of Lemma 3.2 (ibid., p. 19, "y^{−1} := (y_v^{−1})_v"): every
exponent of a vertex variable changes sign; `x, x′, w` are fixed. -/
noncomputable def invY {n : ℕ} (F : LPoly n) : LPoly n :=
  AddMonoidAlgebra.mapDomain
    (fun e : Var n →₀ ℤ => e.filter (fun z => ¬ IsYVar z) - e.filter (fun z => IsYVar z)) F

/-- The Laurent monomial `Π_{v ∈ W} y_v`. -/
noncomputable def yProdL {n : ℕ} (W : Finset (Fin n)) : LPoly n :=
  AddMonoidAlgebra.single (∑ v ∈ W, Finsupp.single (Var.y v) (1 : ℤ)) 1

/-- **`B_t`-support** of a monomial. ibid., §3.3, p. 20: "For a monomial m = x^b w^ℓ
Π_{v ∈ V(G_t)} y_v^{a_v}, call {v ∈ B_t : a_v > 0} the B_t-support of m." -/
noncomputable def bSupp {n : ℕ} (B : Finset (Fin n)) (e : Var n →₀ ℕ) : Finset (Fin n) :=
  B.filter (fun v => 0 < e (Var.y v))

/-- **L_{t,S}(y, w).** ibid., §3.3, p. 20: "For each S ⊆ B_t, let L_{t,S}(y, w) be the formal power
series consisting of the terms of log Z_t^{≤2k}(y, w) whose monomials have B_t-support S."
`W` plays `V(G_t)`, `B` plays `B_t`; `logPS` is (2). -/
noncomputable def LtS {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (k : ℕ)
    (S : Finset (Fin n)) : MvPowerSeries (Var n) ℚ :=
  discard {e | bSupp B e ≠ S} (logPS (Zle G W B k : MvPowerSeries (Var n) ℚ))

/-- **`⟨F⟩_{≤(k,n,2k)}`.** ibid., §3.3, p. 20: "⟨F⟩_{≤(k,n,2k)} := ⟨F⟩_{deg_w ≤ k, deg_x ≤ n,
Σ_{v ∈ B_t} deg_{y_v} ≤ 2k}". `B` plays `B_t` and `N` plays `n = |V(G)|`. -/
noncomputable def truncKNB {n : ℕ} (k N : ℕ) (B : Finset (Fin n)) (F : MvPowerSeries (Var n) ℚ) :
    MvPowerSeries (Var n) ℚ :=
  discard {e | ¬ (e Var.w ≤ k ∧ e Var.x ≤ N ∧ ∑ v ∈ B, e (Var.y v) ≤ 2 * k)} F

end SingleExpBisect.Main


