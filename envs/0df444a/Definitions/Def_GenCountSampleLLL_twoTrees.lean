-- Prove2me | Definitions.Def_GenCountSampleLLL_twoTrees
-- name    : GenCountSampleLLL_twoTrees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:59.795268+00:00
-- url     : https://prove2.me/theorems/5b178cc1-6919-4f5e-8904-5987f7315c01
-- title:
--   Rooted 2-trees, the selection procedure, $E_{\mathcal T}$, $\theta_{\mathcal T}$, $\mathcal D_{\mathcal T,i}$, $\lambda_{\mathcal T}$, $\rho_t$, the pairing $\iota_\sigma$, the list experiment
-- statement:
--   Fix $a\in\mathcal D\subseteq\mathcal C$ and let $G_{\mathcal D}=G[\mathcal D]$. $N_{\mathcal D}[\mathcal T]$ is $\mathcal T$ with its neighbours in $G_{\mathcal D}$ and $N^2_{\mathcal D}[\mathcal T]$ the constraints at distance at most two from $\mathcal T$ in $G_{\mathcal D}$. A **2-tree rooted at $a$** is a set $\mathcal T\subseteq\mathcal D$ containing $a$, independent in $G_{\mathcal D}$ and connected in $G^2_{\mathcal D}$; $\mathfrak T_{\mathcal D,a}$ is the family of them.
--
--   The **selection procedure** on input $\mathcal B$ starts from $\mathcal T_{\mathrm{curr}}=\{a\}$, $\mathcal R=\emptyset$, and repeatedly examines the first constraint $b\in\mathcal D\setminus(\mathcal T_{\mathrm{curr}}\cup\mathcal R)$ at distance exactly two from $\mathcal T_{\mathrm{curr}}$ in $G_{\mathcal D}$, adding it to $\mathcal T_{\mathrm{curr}}$ if $b\in\mathcal B$ and to $\mathcal R$ otherwise; $\mathrm{Tree}_{\mathcal D,a}(\mathcal B)$ is the final accepted set. For $\mathcal T\in\mathfrak T_{\mathcal D,a}$: $\mathcal R(\mathcal T)$ is the rejected set of the run on $\mathcal T$, $\mathcal F(\mathcal T)=\mathcal D\setminus(\mathcal T\cup\mathcal R(\mathcal T))$, $\mathcal F_1(\mathcal T)$ its members adjacent to $\mathcal T$, $\mathcal D_{\mathcal T}=\mathcal D\setminus N^2_{\mathcal D}[\mathcal T]$,
--   $$
--   E_{\mathcal T}=\Big(\bigcap_{b\in\mathcal T}B_b\Big)\cap\Big(\bigcap_{b\in\mathcal F_1(\mathcal T)}B_b^{c}\Big),\qquad U_{\mathcal T}=\mathrm{vbl}(N_{\mathcal D}[\mathcal T]),\qquad \theta_{\mathcal T}=\nu(E_{\mathcal T}),
--   $$
--   $E^\star_{\mathcal T}=E_{\mathcal T}\cap\mathrm{Good}(\mathcal D_{\mathcal T})$, $b_{\mathcal T,1},\dots,b_{\mathcal T,\ell(\mathcal T)}$ the constraints of $N^2_{\mathcal D}[\mathcal T]\setminus\{a\}$ in order, $\mathcal D_{\mathcal T,i}=\mathcal D_{\mathcal T}\cup\{b_{\mathcal T,1},\dots,b_{\mathcal T,i}\}$, $\lambda_{\mathcal T}=(-1)^{|\mathcal T|-1}Z_{\mathcal D_{\mathcal T}}/Z_{\mathcal D}$, $\ell_x(\mathcal T)=\sum_{b\in N^2_{\mathcal D}[\mathcal T]\setminus\{a\}}x_b$, $j_b=e^{16cx_b}$ and $\rho_t=p_t\prod_{b\in N^2_G[t]}j_b$.
--
--   For $\sigma\in\Omega$, $\mathcal Q(\sigma)$ is the set of constraints of $\mathcal D$ violated by $\sigma$, $d_\sigma(\mathcal T)$ the last constraint of $\mathcal Q(\sigma)\setminus\{a\}$ examined on input $\mathcal T$, and $\iota_\sigma(\mathcal T)=\mathcal T\triangle\{d_\sigma(\mathcal T)\}$. In the **list experiment** each $b\in\mathcal D$ draws $\sigma_b\sim\nu_{\mathrm{vbl}(b)}$ independently ($b$ is *active* if $\sigma_b$ violates $b$), each tree's assignment $\sigma_{\mathcal T}$ combines the $\sigma_t$, $t\in\mathcal T$, and is completed on $U_{\mathcal T}$ with fresh samples; $\mathbf L=\{(\mathcal T,\sigma_{\mathcal T}):\sigma_{\mathcal T}\in E_{\mathcal T}\}$, and $\mathbf L^e$ is the list of the experiment pinned at $e=(\mathcal T,z)$.
--
--   These objects carry the 2-tree expansion, the estimator and the insertion chain.
--
--   **Formalization Note** "First" is the least constraint in the order of `Fin m`; the run is iterated $m$ times, which suffices. $b_{\mathcal T,i}$ is read for $1\le i\le\ell(\mathcal T)$, and $\iota_\sigma(\mathcal T)=\mathcal T$ when $d_\sigma(\mathcal T)$ is undefined (a case every statement excludes). An element $z\in E_{\mathcal T}\subseteq\Omega_{U_{\mathcal T}}$ is a full assignment set to $0$ outside $U_{\mathcal T}$. The experiment draws one full assignment per constraint and per set of constraints; only their parts on $\mathrm{vbl}(b)$, resp. $U_{\mathcal T}\setminus\mathrm{vbl}(\mathcal T)$, are read, so the laws are the page's. `numConn` counts the connected sets of Lemma 3.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), §2.1, pp.8–10; §3, pp.11–15; §5.2, p.19

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

noncomputable section

open Classical

/-!
# Rooted 2-trees, the selection procedure, and the tree-indexed objects

Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671
(held file sha256 cd449f83…), §2.1 (pp.8–10), §3 (pp.11–15), §5.2 (p.19).

**Formalization Note.** All objects are for a fixed rooted instance `(D, a)` with `D ⊆ C`
(`D : Finset (Fin m)`), in the graph `G_D = G[D]`: a path in `G_D` has all its vertices in `D`.
Neighbourhoods follow the page: `N_D[T]` and `N²_D[T]` are closed and taken in `G_D` (p.8);
`N²_G[t]` is closed and taken in `G` (p.13). "The first constraint" in the selection procedure is
the least one in the order of `Fin m` (the fixed ordering `a₁, …, a_m` of p.7). The procedure is
run for `m` examinations, enough because each examination moves a new constraint of `D` into the
accepted or rejected set. The list `b_{T,1}, …, b_{T,ℓ(T)}` lists `N²_D[T] ∖ {a}` in increasing
order; `b_{T,i}` is read for `1 ≤ i ≤ ℓ(T)` only. The list experiment draws one full assignment
per constraint and one per finite set of constraints; constraint `b` uses only its draw on
`vbl(b)`, and the completion for `T` only its draw on `U_T ∖ vbl(T)`, so the law of everything
used is the page's (independent `σ_b ∼ ν_{vbl(b)}` and independent completions `∼ ν`). An element
`z ∈ Ω_{U_T}` is stored as a full assignment normalized to `0` outside `U_T`.
-/

namespace Inst

variable (I : Inst)

/-- `t` and `b` are at distance one or two in `G_D` (the intermediate vertex lies in `D`). -/
def adj2D (D : Finset (Fin I.m)) (t b : Fin I.m) : Prop :=
  I.G.Adj t b ∨ ∃ c ∈ D, I.G.Adj t c ∧ I.G.Adj c b

/-- The square `G²_D = (G_D)²` of `G_D = G[D]`, as a graph on `Fin m` whose edges lie in `D`. -/
def sqD (D : Finset (Fin I.m)) : SimpleGraph (Fin I.m) where
  Adj u v := u ≠ v ∧ u ∈ D ∧ v ∈ D ∧ I.adj2D D u v
  symm := { symm := fun u v h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    rcases h.2.2.2 with h' | ⟨c, hc, h1, h2⟩
    · exact Or.inl h'.symm
    · exact Or.inr ⟨c, hc, h2.symm, h1.symm⟩⟩ }
  loopless := { irrefl := fun u h => h.1 rfl }

/-- `N_D[T]`: `T` together with its neighbours in `G_D` (closed, p.8). -/
def NDc (D T : Finset (Fin I.m)) : Finset (Fin I.m) :=
  T ∪ D.filter fun b => ∃ t ∈ T, I.G.Adj t b

/-- `N²_D[T]`: the constraints of `D` at distance at most two from `T` in `G_D` (closed, p.8). -/
def N2Dc (D T : Finset (Fin I.m)) : Finset (Fin I.m) :=
  T ∪ D.filter fun b => ∃ t ∈ T, I.adj2D D t b

/-- `T` is a 2-tree rooted at `a` in `D` (p.8): `T ⊆ D`, `a ∈ T`, `T` is independent in `G_D`, and
`T` is connected in `G²_D`. -/
def IsTwoTree (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Prop :=
  T ⊆ D ∧ a ∈ T ∧ (∀ u ∈ T, ∀ v ∈ T, ¬ I.G.Adj u v) ∧
    ((I.sqD D).induce (T : Set (Fin I.m))).Connected

/-- `T_{D,a}`, the family of 2-trees rooted at `a` (p.8). -/
def twoTrees (D : Finset (Fin I.m)) (a : Fin I.m) : Finset (Finset (Fin I.m)) :=
  D.powerset.filter (I.IsTwoTree D a)

/-- A state of the selection procedure: the accepted set `T_curr`, the rejected set `R`, and the
examined constraints in the order of examination. -/
structure SelState (m : ℕ) where
  /-- The accepted set `T_curr`. -/
  acc : Finset (Fin m)
  /-- The rejected set `R`. -/
  rej : Finset (Fin m)
  /-- The examined constraints, in order. -/
  ex : List (Fin m)

/-- The constraints `b ∈ D ∖ (T_curr ∪ R)` at distance exactly two from `T_curr` in `G_D`. -/
def eligible (D : Finset (Fin I.m)) (s : SelState I.m) : Finset (Fin I.m) :=
  (D \ (s.acc ∪ s.rej)).filter fun b =>
    (∀ t ∈ s.acc, ¬ I.G.Adj t b) ∧ ∃ t ∈ s.acc, ∃ c ∈ D, I.G.Adj t c ∧ I.G.Adj c b

/-- One step of the selection procedure on input `B` (p.8): examine the first eligible
constraint `b`, add it to `T_curr` if `b ∈ B` and to `R` otherwise; stay put if none is
eligible. -/
def selStep (D B : Finset (Fin I.m)) (s : SelState I.m) : SelState I.m :=
  if h : (I.eligible D s).Nonempty then
    let b := (I.eligible D s).min' h
    if b ∈ B then ⟨insert b s.acc, s.rej, s.ex ++ [b]⟩ else ⟨s.acc, insert b s.rej, s.ex ++ [b]⟩
  else s

/-- The final state of the selection procedure on input `B`, from `T_curr = {a}`, `R = ∅`. -/
def selRun (D : Finset (Fin I.m)) (a : Fin I.m) (B : Finset (Fin I.m)) : SelState I.m :=
  (I.selStep D B)^[I.m] ⟨{a}, ∅, []⟩

/-- `Tree_{D,a}(B)`, the accepted set at termination (p.8). -/
def Tree (D : Finset (Fin I.m)) (a : Fin I.m) (B : Finset (Fin I.m)) : Finset (Fin I.m) :=
  (I.selRun D a B).acc

/-- `R(T)`, the set rejected by the procedure with input `T` (p.8). -/
def Rej (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset (Fin I.m) :=
  (I.selRun D a T).rej

/-- `F(T) = D ∖ (T ∪ R(T))`, the constraints never examined in the run on `T` (p.8). -/
def Fset (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset (Fin I.m) :=
  D \ (T ∪ I.Rej D a T)

/-- `F₁(T)`, the constraints of `F(T)` adjacent to a member of `T` (p.8). -/
def F1 (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset (Fin I.m) :=
  (I.Fset D a T).filter fun b => ∃ t ∈ T, I.G.Adj t b

/-- `D_T = D ∖ N²_D[T]`, the constraints of `D` at distance greater than two from `T` (p.8). -/
def DT (D T : Finset (Fin I.m)) : Finset (Fin I.m) := D \ I.N2Dc D T

/-- `σ ∈ E_T = (⋂_{b∈T} B_b) ∩ (⋂_{b∈F₁(T)} B_b^c)` (p.9). -/
def inET (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) (σ : I.Assign) : Prop :=
  (∀ b ∈ T, I.bad b σ) ∧ ∀ b ∈ I.F1 D a T, ¬ I.bad b σ

/-- `E_T` as a set of assignments of `Ω`. -/
def ET (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset I.Assign :=
  Finset.univ.filter (I.inET D a T)

/-- `U_T = vbl(N_D[T])` (p.9). -/
def UT (D T : Finset (Fin I.m)) : Finset (Fin I.n) := (I.NDc D T).biUnion I.vbl

/-- `E⋆_T = E_T ∩ Good(D_T)` (p.17). -/
def Estar (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset I.Assign :=
  I.ET D a T ∩ I.Good (I.DT D T)

/-- The labels `z ∈ E_T ⊆ Ω_{U_T}`, stored normalized to `0` outside `U_T`. -/
def labelsE (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : Finset I.Assign :=
  (I.ET D a T).filter fun z => z = I.restr (I.UT D T) z

/-- `θ_T = ν(E_T)` (p.9). -/
def theta (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : ℝ :=
  ∑ σ ∈ I.ET D a T, I.nuA σ

/-- `b_{T,1}, …, b_{T,ℓ(T)}`: the constraints of `N²_D[T] ∖ {a}` in the induced order (p.10). -/
def bList (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : List (Fin I.m) :=
  ((I.N2Dc D T).erase a).sort (· ≤ ·)

/-- `ℓ(T) = |N²_D[T] ∖ {a}|` (p.10). -/
def ell (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : ℕ :=
  (I.bList D a T).length

/-- `b_{T,i}` for `1 ≤ i ≤ ℓ(T)` (p.10). -/
def bT (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) (i : ℕ) : Fin I.m :=
  (I.bList D a T).getD (i - 1) a

/-- `D_{T,i} = D_T ∪ {b_{T,1}, …, b_{T,i}}` for `0 ≤ i ≤ ℓ(T)` (p.10). -/
def DTi (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) (i : ℕ) :
    Finset (Fin I.m) :=
  I.DT D T ∪ ((I.bList D a T).take i).toFinset

/-- `λ_T = (−1)^{|T|−1} Z_{D_T}/Z_D` (p.10). -/
def lam (D : Finset (Fin I.m)) (T : Finset (Fin I.m)) : ℝ :=
  (-1 : ℝ) ^ (T.card - 1) * I.Z (I.DT D T) / I.Z D

/-- `ℓ_x(T) = Σ_{b ∈ N²_D[T] ∖ {a}} x_b` (p.15). -/
def ellx (x : Fin I.m → ℝ) (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) : ℝ :=
  ∑ b ∈ (I.N2Dc D T).erase a, x b

/-- `j_b = e^{16 c x_b}` (p.12). -/
def jfun (c : ℝ) (x : Fin I.m → ℝ) (b : Fin I.m) : ℝ := Real.exp (16 * c * x b)

/-- The global weights `ρ_t = p_t ∏_{b ∈ N²_G[t]} j_b` (p.13). -/
def rho (c : ℝ) (x : Fin I.m → ℝ) (t : Fin I.m) : ℝ :=
  I.p t * ∏ b ∈ I.N2Gc t, I.jfun c x b

/-- `Q(σ) = {b ∈ D : σ ∈ B_b}`, the constraints of `D` violated by `σ` (p.19). -/
def Qv (D : Finset (Fin I.m)) (σ : I.Assign) : Finset (Fin I.m) := D.filter fun b => I.bad b σ

/-- `d_σ(T)`, the last constraint of `Q(σ) ∖ {a}` examined by the selection procedure on input
`T` (p.19); `none` if no such constraint is examined. -/
def dSig (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) (σ : I.Assign) :
    Option (Fin I.m) :=
  ((I.selRun D a T).ex.filter fun b => decide (b ∈ (I.Qv D σ).erase a)).getLast?

/-- `ι_σ(T) = T △ {d_σ(T)}` (p.19); `T` itself when `d_σ(T)` is undefined (a case excluded by
every statement using it). -/
def iota (D : Finset (Fin I.m)) (a : Fin I.m) (T : Finset (Fin I.m)) (σ : I.Assign) :
    Finset (Fin I.m) :=
  match I.dSig D a T σ with
  | some d => symmDiff T {d}
  | none => T

/-- The sample space of the list experiment: one full assignment for each constraint (`inl b`,
the local draw `σ_b`, used on `vbl(b)`) and one for each set of constraints (`inr T`, the
completion for `T`, used on `U_T ∖ vbl(T)`). -/
abbrev ExpSpace : Type := Fin I.m ⊕ Finset (Fin I.m) → I.Assign

/-- The law of the list experiment: all draws independent with law `ν` (p.11, p.19). -/
def expLaw : PMF I.ExpSpace := piLaw fun _ => I.prodLaw

/-- `σ_T ∈ Ω_{U_T}` (p.11): the local draws `σ_t`, `t ∈ T`, combined on `vbl(T)` and completed on
`U_T ∖ vbl(T)` by the completion for `T`; normalized to `0` outside `U_T`. For a 2-tree the sets
`vbl(t)`, `t ∈ T`, are disjoint, so the choice of `t` is immaterial. -/
def sigT (D T : Finset (Fin I.m)) (ω : I.ExpSpace) : I.Assign :=
  I.restr (I.UT D T) fun v =>
    if h : ∃ t, t ∈ T ∧ v ∈ I.vbl t then ω (Sum.inl h.choose) v else ω (Sum.inr T) v

/-- The constraints of `D` active in the experiment: `σ_b` violates `b` (p.11). -/
def active (D : Finset (Fin I.m)) (ω : I.ExpSpace) : Finset (Fin I.m) :=
  D.filter fun b => I.bad b (ω (Sum.inl b))

/-- The random list `L = {(T, σ_T) : T ∈ T_{D,a}, σ_T ∈ E_T}` (p.19). -/
def Llist (D : Finset (Fin I.m)) (a : Fin I.m) (ω : I.ExpSpace) :
    Finset (Finset (Fin I.m) × I.Assign) :=
  ((I.twoTrees D a).filter fun T => I.inET D a T (I.sigT D T ω)).image
    fun T => (T, I.sigT D T ω)

/-- The experiment pinned at `e = (T, z)` (p.19): `σ_t = z|_{vbl(t)}` for `t ∈ T` and the
completion for `T` equal to `z`; every other draw unchanged. -/
def pin (e : Finset (Fin I.m) × I.Assign) (ω : I.ExpSpace) : I.ExpSpace := fun j =>
  match j with
  | Sum.inl b => if b ∈ e.1 then e.2 else ω (Sum.inl b)
  | Sum.inr T => if T = e.1 then e.2 else ω (Sum.inr T)

/-- The conditioned list `L_e`, the list of the experiment pinned at `e` (p.19). -/
def Le (D : Finset (Fin I.m)) (a : Fin I.m) (e : Finset (Fin I.m) × I.Assign)
    (ω : I.ExpSpace) : Finset (Finset (Fin I.m) × I.Assign) :=
  I.Llist D a (I.pin e ω)

/-- The number of sets `B` of active constraints with `a ∈ B` and `G²_D[B]` connected: the
quantity `A` of Lemma 3.4 (p.15), as a function of the active set `S`. -/
def numConn (D : Finset (Fin I.m)) (a : Fin I.m) (S : Finset (Fin I.m)) : ℕ :=
  (S.powerset.filter fun B => a ∈ B ∧ ((I.sqD D).induce (B : Set (Fin I.m))).Connected).card

end Inst

end

end GenCountSampleLLL


