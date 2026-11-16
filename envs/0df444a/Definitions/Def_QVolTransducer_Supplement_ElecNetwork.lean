-- Prove2me | Definitions.Def_QVolTransducer_Supplement_ElecNetwork
-- name    : QVolTransducer_Supplement_ElecNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:05.590971+00:00
-- url     : https://prove2.me/theorems/36980450-02cd-49cb-960a-ac8108faad15
-- title:
--   Electrical networks, flows, effective resistance and the transducer $T=A^\dagger(U\oplus I)A$
-- statement:
--   An **electrical network** $(G=(V,E),r)$ is a connected undirected graph on a finite vertex set (self-loops allowed, no multiple edges, every vertex with a neighbour) with resistances $r:E\to\mathbb R_{>0}$. Write
--
--   $$r_v=\Big(\sum_{w\in N(v)}\frac1{r_{vw}}\Big)^{-1},\qquad R=\Big(\sum_{v}\frac1{r_v}\Big)^{-1},\qquad P(v,w)=\frac{r_v}{r_{vw}}\ (vw\in E),\qquad \pi_v=\frac{R}{r_v}.$$
--
--   The star state is $|*_v\rangle=\sum_{w\in N(v)}\sqrt{r_v/r_{vw}}\,|w\rangle$, $N|v\rangle=|v\rangle|*_v\rangle$, $H_1=\mathrm{Span}\{|v\rangle|*_v\rangle\}$ and $H_2=\mathrm{Span}\{|v,w\rangle+|w,v\rangle\}$ inside $\mathcal H=(\mathbb C^V)^{\otimes2}$. A **flow** $f:E\to\mathbb C$ has net-flow $\delta_f(v)=\sum_{e\in N^+(v)}f_e-\sum_{e\in N^-(v)}f_e$ and energy $\sum_e|f_e|^2r_e$; the **effective resistance** of a net-flow $\delta$ is
--
--   $$R_{\mathrm{eff}}(G,r;\delta)=\min_{f:\,\delta_f=\delta}\sum_{e\in E}|f_e|^2r_e,$$
--
--   and a flow is embedded as $|f\rangle=\sum_{vw\in E}f_{vw}\sqrt{r_{vw}}(|v,w\rangle-|w,v\rangle)$. Finally $U=(2\Pi_{H_1}-I)(2\Pi_{H_2}-I)$, $A=(H\otimes I_{\mathcal H})(I_{\mathcal H}\oplus(2\Pi_{H_1}-I_{\mathcal H}))(H\otimes I_{\mathcal H})$ with the Hadamard $H$, and $T=A^\dagger(U\oplus I_{\mathcal H})A$; the transduction complexity of $U$ with public space $H_1$ and private space $H_1^\perp$ is also defined.
--
--   These objects are the setting of Theorem 4.4, the walk-based reflection through the stationary state.
--
--   **Formalization Note** Edges are a symmetric Boolean adjacency; resistances a symmetric function whose off-edge values are unused. Flows are antisymmetric functions $F(v,w)=-F(w,v)$ supported on edges, which avoids choosing an orientation ($F(v,w)=f_e$ if $e$ is oriented $v\to w$); self-loops then carry no flow, which changes neither net-flows nor minimum energies. $\Pi_{H_1}=\sum_v|v\rangle\langle v|\otimes|*_v\rangle\langle*_v|$ (the star states are orthonormal unit vectors) and $\Pi_{H_2}=(I+\mathrm{SWAP})/2$. $H^{\oplus2}$ is $\mathbb C^{(V\times V)\oplus(V\times V)}$ with the public summand first.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), §2.1 p.11, Definitions 2.20 and 2.23 p.16 (PDF pp.13, 18), Definition 4.1 and Lemmas 4.2–4.3, pp.28–29, Theorem 4.4, p.30 (PDF pp.30–32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_transductionComplexity
import Definitions.Def_QVolTransducer_starState

namespace QVolTransducer.Supplement

open QAlgorithms

/-- An **electrical network** `(G = (V, E), r)` (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), §2.1, p.11, and Definition 2.20, p.16): a connected undirected
graph on the finite vertex set `V`, allowing self-loops but no multiple edges, with a resistance
`r_{vw} > 0` on every edge, every vertex having at least one neighbour.

**Formalization Note** The edge set is the symmetric adjacency relation `adj` (`adj v v` is a
self-loop); `r` is a symmetric function on vertex pairs whose values off the edges are never used.
Connectivity is the reflexive–transitive closure of `adj` relating every two vertices. -/
structure ElecNetwork (V : Type*) [Fintype V] where
  /-- The adjacency relation of the undirected graph `G` (self-loops allowed). -/
  adj : V → V → Bool
  /-- The resistance function `r : E → ℝ_{>0}`. -/
  r : V → V → ℝ
  adj_symm : ∀ v w, adj v w = adj w v
  r_symm : ∀ v w, r v w = r w v
  r_pos : ∀ v w, adj v w = true → 0 < r v w
  nbr : ∀ v, ∃ w, adj v w = true
  conn : ∀ v w, Relation.ReflTransGen (fun a b => adj a b = true) v w

namespace ElecNetwork

variable {V : Type*} [Fintype V] (G : ElecNetwork V)

open Classical in
/-- `r_v := (Σ_{w ∈ N(v)} 1/r_{vw})^{−1}` (arXiv:2609.40217, Definition 2.20, p.16; a self-loop
contributes `1/r_{vv}` once). -/
noncomputable def rv (v : V) : ℝ :=
  (∑ w ∈ Finset.univ.filter (fun w => G.adj v w = true), 1 / G.r v w)⁻¹

/-- `R := (Σ_{v∈V} 1/r_v)^{−1}` (arXiv:2609.40217, Definition 2.20, p.16). -/
noncomputable def totalR : ℝ :=
  (∑ v, 1 / G.rv v)⁻¹

/-- The random walk on the network, `P(v, w) := r_v / r_{vw}` if `vw ∈ E` and `0` otherwise
(arXiv:2609.40217, Definition 2.20, p.16). -/
noncomputable def walk : Matrix V V ℝ :=
  fun v w => if G.adj v w = true then G.rv v / G.r v w else 0

/-- The stationary distribution `π_v = R / r_v` of the walk (arXiv:2609.40217, Theorem 2.21,
p.16; with `R = 1`, `π_v = 1/r_v`, p.29). -/
noncomputable def stat (v : V) : ℝ :=
  G.totalR / G.rv v

/-- The isometry `N : ℂ^V → (ℂ^V)^{⊗2}`, `N|v⟩ = |v⟩|∗_v⟩` with the star state
`|∗_v⟩ = Σ_{w∈N(v)} √(r_v/r_{vw}) |w⟩` (arXiv:2609.40217, Definition 4.1, p.28); the star state
is the published `QVolTransducer.starState` of the walk. -/
noncomputable def Nmap [DecidableEq V] (ψ : EuclideanSpace ℂ V) : EuclideanSpace ℂ (V × V) :=
  WithLp.toLp 2 (fun p => ψ p.1 * starState G.walk p.1 p.2)

/-- The orthogonal projection `Π_{H_1}` onto `H_1 = Span{|v⟩|∗_v⟩ : v ∈ V}` (arXiv:2609.40217,
Definition 4.1, p.28), as the matrix `Σ_v |v⟩⟨v| ⊗ |∗_v⟩⟨∗_v|`.

**Formalization Note** Each star state is a unit vector (`Σ_{w∈N(v)} r_v/r_{vw} = 1`), and the
vectors `|v⟩|∗_v⟩` are orthonormal, so this matrix is the orthogonal projection onto `H_1`. -/
noncomputable def proj1 [DecidableEq V] : Matrix (V × V) (V × V) ℂ :=
  fun p q => if p.1 = q.1 then starState G.walk p.1 p.2 * starState G.walk q.1 q.2 else 0

/-- The orthogonal projection `Π_{H_2} = (I + SWAP)/2` onto the symmetric subspace
`H_2 = Span{|v, w⟩ + |w, v⟩ : v, w ∈ V}` of `(ℂ^V)^{⊗2}` (arXiv:2609.40217, Definition 4.1,
p.28). -/
noncomputable def proj2 (V : Type*) [DecidableEq V] : Matrix (V × V) (V × V) ℂ :=
  fun p q => ((if p = q then 1 else 0) + (if p = q.swap then 1 else 0)) / 2

/-- The transducer `U = (2Π_{H_1} − I)(2Π_{H_2} − I) ∈ U((ℂ^V)^{⊗2})` of Lemma 4.3
(arXiv:2609.40217, p.29). -/
noncomputable def Uop [DecidableEq V] : Matrix (V × V) (V × V) ℂ :=
  (2 • G.proj1 - 1) * (2 • proj2 V - 1)

/-- The operator `A = (H ⊗ I_H)(I_H ⊕ (2Π_{H_1} − I_H))(H ⊗ I_H)` on `H^{⊕2}`, with the `2×2`
Hadamard `H = (1/√2)[[1, 1], [1, −1]]` (arXiv:2609.40217, Theorem 4.4, p.30). `H^{⊕2}` is
`ℂ^((V×V) ⊕ (V×V))`, its first summand being the public space. -/
noncomputable def Aop [DecidableEq V] :
    Matrix ((V × V) ⊕ (V × V)) ((V × V) ⊕ (V × V)) ℂ :=
  let had : Matrix ((V × V) ⊕ (V × V)) ((V × V) ⊕ (V × V)) ℂ :=
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • Matrix.fromBlocks 1 1 1 (-1)
  had * Matrix.fromBlocks 1 0 0 (2 • G.proj1 - 1) * had

/-- The transducer `T = A†(U ⊕ I_H)A` of Theorem 4.4 (arXiv:2609.40217, p.30), with public space
`H = (ℂ^V)^{⊗2}` (first summand) and private space `H` (second summand). -/
noncomputable def Top [DecidableEq V] :
    Matrix ((V × V) ⊕ (V × V)) ((V × V) ⊕ (V × V)) ℂ :=
  G.Aop.conjTranspose * Matrix.fromBlocks G.Uop 0 0 1 * G.Aop

/-- The transduction complexity of Lemma 4.3's transducer `U` with public space `H_1` and private
space `H_1^⊥` (arXiv:2609.40217, Lemma 4.3, p.29, and Definition 2.7, p.13), on the public vector
`N|ψ⟩`: `W(U, |ψ⟩) := inf{‖|w⟩‖² : |w⟩ ∈ H_1^⊥, U(N|ψ⟩ + |w⟩) = N|τ⟩ + |w⟩ for some |τ⟩}`. -/
noncomputable def lemma43Complexity [DecidableEq V] (ψ : EuclideanSpace ℂ V) : ℝ :=
  sInf {c : ℝ | ∃ (τ : EuclideanSpace ℂ V) (w : EuclideanSpace ℂ (V × V)),
    act G.proj1 w = 0 ∧ act G.Uop (G.Nmap ψ + w) = G.Nmap τ + w ∧ c = ‖w‖ ^ 2}

/-- A flow `f : E → ℂ` (arXiv:2609.40217, Definition 2.23, p.16), represented without a choice of
orientation as an antisymmetric function `F(v, w) = −F(w, v)` on vertex pairs supported on the
edges: `F(v, w) = f_e` if the edge `e = vw` is oriented from `v` to `w`, and `−f_e` otherwise.

**Formalization Note** A self-loop carries flow `0` (antisymmetry); a flow on a self-loop changes no
net-flow and only adds energy, so the minimum-energy flows and the effective resistance are those of
Definition 2.23. -/
def IsFlow (F : V → V → ℂ) : Prop :=
  (∀ v w, F v w = -F w v) ∧ ∀ v w, G.adj v w = false → F v w = 0

/-- The net-flow `δ_f(v) = Σ_{e ∈ N^+(v)} f_e − Σ_{e ∈ N^−(v)} f_e = Σ_w F(v, w)`
(arXiv:2609.40217, Definition 2.23, p.16). -/
noncomputable def netFlow (F : V → V → ℂ) (v : V) : ℂ :=
  ∑ w, F v w

/-- The energy `‖|f⟩‖² = Σ_{e∈E} |f_e|² r_e` of a flow (arXiv:2609.40217, Definition 2.23, p.16):
every edge appears twice among the ordered pairs, hence the factor `1/2`. -/
noncomputable def energy (F : V → V → ℂ) : ℝ :=
  (1 / 2) * ∑ v, ∑ w, ‖F v w‖ ^ 2 * G.r v w

/-- The effective resistance `R_eff(G, r; δ) := min{‖|f⟩‖² : f : E → ℂ, δ_f = δ}` of a net-flow
`δ ∈ ℂ^V` (arXiv:2609.40217, Definition 2.23, p.16).

**Formalization Note** Written as an infimum of a set of nonnegative reals; for a net-flow
(`Σ_v δ_v = 0`) on a connected network the set is nonempty and the minimum is attained. -/
noncomputable def effRes (δ : V → ℂ) : ℝ :=
  sInf {e : ℝ | ∃ F, G.IsFlow F ∧ netFlow F = δ ∧ e = G.energy F}

/-- `F` is a minimum-energy flow with net-flow `δ` (the flow `f^δ` of Lemma 4.2, arXiv:2609.40217,
p.29). -/
def IsMinEnergyFlow (F : V → V → ℂ) (δ : V → ℂ) : Prop :=
  G.IsFlow F ∧ netFlow F = δ ∧
    ∀ F', G.IsFlow F' → netFlow F' = δ → G.energy F ≤ G.energy F'

/-- The embedding `|f⟩ := Σ_{vw∈E} f_{vw} √r_{vw} (|v, w⟩ − |w, v⟩) ∈ (ℂ^V)^{⊗2}` of a flow
(arXiv:2609.40217, Lemma 4.2, p.29); in the antisymmetric representation its `(v, w)` entry is
`F(v, w) √r_{vw}`. -/
noncomputable def flowEmbed (F : V → V → ℂ) : EuclideanSpace ℂ (V × V) :=
  WithLp.toLp 2 (fun p => F p.1 p.2 * ((Real.sqrt (G.r p.1 p.2) : ℝ) : ℂ))

end ElecNetwork

end QVolTransducer.Supplement


