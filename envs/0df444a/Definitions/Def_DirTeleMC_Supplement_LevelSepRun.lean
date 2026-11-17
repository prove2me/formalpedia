-- Prove2me | Definitions.Def_DirTeleMC_Supplement_LevelSepRun
-- name    : DirTeleMC_Supplement_LevelSepRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:41:20.163422+00:00
-- url     : https://prove2.me/theorems/bebbd164-5787-4a94-a06e-2ec06a3c96bf
-- title:
--   LEVELSEP: the separator recursion for a guess $\theta$
-- statement:
--   Fix $p$, a separator algorithm, a guess $\theta$ and a rational $x$ feasible for LP($\theta$). Let $k=|K|$, $\bar d=\lfloor\log_2k\rfloor$, $\sigma=\min\{p,k\}$, $\epsilon=1/(2(\bar d+1))$, $\delta=1/100$ and $\beta=7/(4\epsilon)$.
--
--   An **instance** is a pair $(R,W)$ of a root set and a region, with terminals $K\cap W$; its entry arcs are the arcs of $G_{\le\theta}$ from $R$ into $W$ and its internal arcs those inside $W$. In an instance of depth $d$, the **entry mass** of $u\in R$ is $m(u)=\sum_{v\in W}(1-\epsilon)^{-d}x_{uv}$ over the arcs $(u,v)$ of $G_{\le\theta}$.
--
--   **LEVELSEP** starts with level $0$, the instance $(\{s\},V_{\le\theta}\setminus\{s\})$, and processes the levels in turn, the instances of a level one after the other in any order, with loads $\ell(u)=0$ and future masses $\bar m(u)=\sum_j m_{I_j}(u)$ at the start of the level. Processing $I_j$:
--
--   1. $\bar m\leftarrow\bar m-m_{I_j}$; choose rationals $\tilde\omega(u)\in[\omega(u),e^\delta\omega(u)]$ for $u\in R$, where $\omega(u)=\exp(\ell(u)/\sigma+\beta\bar m(u))$;
--   2. $\Omega_j=\sum_{u\in R}\tilde\omega(u)m_{I_j}(u)$; an entry arc with tail $u$ is cheap if $\tilde\omega(u)\le\Omega_j/\epsilon$;
--   3. $H'_j$ is induced by the root $r$ and the vertices reached from $r$ by a walk with at most $\theta$ arcs whose first arc is cheap; $A_j$ is a breadth-first out-arborescence of $H'_j$ without its non-cheap entry arcs; if a terminal of $I_j$ is missing from $H'_j$, the run fails;
--   4. the separator $S_j$ is the root path to the terminal if $I_j$ has one terminal; otherwise, if $p\le k$, the root paths to the vertices the separator algorithm returns on the underlying graphs of $H'_j$ and $A_j$ with weights $1$ on the terminals; if $p>k$, the root paths to all terminals; the piece is the set of arcs of $A_j$ into $S_j$;
--   5. $\ell(u)$ grows by the number of arcs of the piece that leave $r$ with tail $u$;
--   6. every weakly connected component $C$ of $H'_j-S_j$ with a terminal becomes the child $(R\cup(S_j\setminus\{r\}),C)$ at the next level.
--
--   The result is failure or the list of pieces with their depths. It feeds the phase schedule and LPSEP.
--
--   **Formalization Note** The run is an inductive relation; every free choice is open (instance orders, the weights $\tilde\omega$, the breadth-first tree, and the numbering of $H'_j$ given to the separator algorithm). A piece is recorded by its depth, the root set, its vertices other than $r$ and the parent map.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), App. C.3, "Parameters", "Masses", "Processing an instance", steps (1)–(6), pp.39–40 (PDF pp.40–41); Definitions C.3–C.4, p.39 (PDF p.40); Algorithm 4, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_DirTeleMC_Supplement_LPFeasible
import Definitions.Def_DirTeleMC_Supplement_IsClassAlgorithm

namespace DirTeleMC.Supplement

open DirTeleMC

/-- The fixed data of a run of LEVELSEP (Algorithm 4, p.41): the instance `I` (digraph `G`, source `s`, terminals
`K`), the integer `p` and the class algorithm `Z` (Definition 5.1), the guess `θ`, and the rational vector `x`
computed in line 6. -/
structure LSCtx where
  I : Inst
  p : ℕ
  Z : SepInput → List ℕ
  θ : ℕ
  x : Fin I.n → Fin I.n → ℚ

namespace LSCtx

variable (C : LSCtx)

/-- `d̄ = ⌊log₂ k⌋` with `k = |K|` (App. C.2, p.38). -/
def dbar : ℕ := Nat.log 2 C.I.K.card

/-- `σ = min{p, k}` (App. C.3, p.39). -/
def sigma : ℕ := min C.p C.I.K.card

/-- `ϵ = 1/(2(d̄ + 1))` (App. C.3, p.39). -/
def eps : ℚ := 1 / (2 * ((C.dbar : ℚ) + 1))

/-- `δ = 1/100` (App. C.3, p.39). -/
def delta (_C : LSCtx) : ℚ := 1 / 100

/-- `β = 7/(4ϵ)` (App. C.3, p.39). -/
def beta : ℚ := 7 / (4 * C.eps)

end LSCtx

/-- **An instance of the recursion** (Definition C.3, p.39): a root set `R` and a region `W` (the terminals are
`K ∩ W`). -/
structure SInst (n : ℕ) where
  R : Finset (Fin n)
  W : Finset (Fin n)

/-- A piece with its depth (App. C.3, step (4), p.40): the depth `d` of its instance, the root set `R` of the
instance, the vertices `SW` of the separator other than the root `r`, and the parent map of `A_j`. The arcs of the
piece are `(par v, v)` for `v ∈ SW`; such an arc leaves `r` (an entry arc with G-tail `par v`) iff `par v ∈ R`. -/
structure Piece (n : ℕ) where
  depth : ℕ
  R : Finset (Fin n)
  SW : Finset (Fin n)
  par : Fin n → Fin n

variable (C : LSCtx)

/-- **The entry mass** `m_I(u)` of a vertex `u` in an instance `J` of depth `d` (App. C.3, "Masses", p.39): the sum of
the scaled capacities `x^J_e = (1 − ϵ)^{−d} x_e` of the entry arcs `e = (u, v)`, `v ∈ W`, of `H(J)` with G-tail `u`;
`0` for `u ∉ R`. -/
noncomputable def mass (d : ℕ) (J : SInst C.I.n) (u : Fin C.I.n) : ℝ := by
  classical
  exact if u ∈ J.R then
      ∑ v ∈ J.W.filter (fun v => ArcLe C.I C.θ u v), ((1 - (C.eps : ℝ))⁻¹) ^ d * (C.x u v : ℝ)
    else 0

/-- A walk of `H(J)` from its root `r` with `m` arcs whose first arc is a cheap entry arc, ending at `v`: a cheap
G-tail `u ∈ R` followed by a nonempty list of `m` vertices of `W`, joined by arcs of `G_{≤θ}`. -/
def CheapWalk (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (v : Fin C.I.n) (m : ℕ) : Prop :=
  ∃ u, u ∈ J.R ∧ cheap u ∧ ∃ L : List (Fin C.I.n), L.length = m ∧ (∀ y ∈ L, y ∈ J.W) ∧
    (∀ h, L.head? = some h → ArcLe C.I C.θ u h) ∧ L.IsChain (ArcLe C.I C.θ) ∧ L.getLast? = some v

/-- The vertices of `H′_j` other than `r` (App. C.3, step (3), p.40: "the subdigraph of H(Ij) induced by r and the
vertices that can be reached from r by a directed path with at most θ arcs whose first arc is cheap"). -/
noncomputable def regionReach (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) : Finset (Fin C.I.n) := by
  classical
  exact J.W.filter fun v => ∃ m, m ≤ C.θ ∧ CheapWalk C J cheap v m

/-- The distance from `r` to `v` in `H′_j` without its non-cheap entry arcs (`0` if there is no walk). -/
noncomputable def cheapDist (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (v : Fin C.I.n) : ℕ := by
  classical
  exact if h : ∃ m, CheapWalk C J cheap v m then Nat.find h else 0

/-- **`par` is a breadth-first out-arborescence `A_j`** from `r` of `H′_j` without its non-cheap entry arcs (App. C.3,
step (3), p.40), given by the G-parent of every vertex of `H′_j` other than `r`: every such `v` is entered by the arc
`(par v, v)`, which is a cheap entry arc (`par v ∈ R`, cheap) or an internal arc of `H′_j` (`par v` a vertex of `H′_j`),
and the depth of `v` in the tree (the number of parent steps to leave `W`) is its distance from `r`. -/
def IsBFSArb (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (par : Fin C.I.n → Fin C.I.n) : Prop :=
  ∀ v ∈ regionReach C J cheap,
    ((par v ∈ J.R ∧ cheap (par v)) ∨ par v ∈ regionReach C J cheap) ∧ ArcLe C.I C.θ (par v) v ∧
    (∀ i < cheapDist C J cheap v, par^[i] v ∈ regionReach C J cheap) ∧
    par^[cheapDist C J cheap v] v ∈ J.R

/-- The vertices other than `r` of the root path `A_j[r, v]`: `v, par v, …` down to the last vertex in `W`. -/
noncomputable def rootPathW (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (par : Fin C.I.n → Fin C.I.n)
    (v : Fin C.I.n) : Finset (Fin C.I.n) := by
  classical
  exact (Finset.range (cheapDist C J cheap v)).image fun i => par^[i] v

/-- The underlying graph of `H′_j`, on `r` (`none`) and the vertices of `regionReach` (App. C.3, step (4)): `r` is
adjacent to `v` if some entry arc of `H(J)` enters `v` (cheap or not), and two vertices of `W` if an arc of `G_{≤θ}`
joins them. -/
def underlyingH (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) :
    SimpleGraph (Option (regionReach C J cheap)) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | none, some v => ∃ u ∈ J.R, ArcLe C.I C.θ u v.1
    | some u, some v => ArcLe C.I C.θ u.1 v.1
    | _, _ => False

/-- The underlying graph of `A_j` (App. C.3, step (4)): `r` is adjacent to `v` if `par v ∈ R`, and `u` to `v` if
`par v = u`. -/
def underlyingA (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (par : Fin C.I.n → Fin C.I.n) :
    SimpleGraph (Option (regionReach C J cheap)) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | none, some v => par v.1 ∈ J.R
    | some u, some v => par v.1 = u.1
    | _, _ => False

/-- **The separator** `S_j` of step (4) (App. C.3, p.40, and SEP, Algorithm 4, lines 1–4), by its vertices other
than `r`: if `J` has a single terminal `t`, the root path `A_j[r, t]`; otherwise, if `p ≤ k`, the root paths to the
vertices other than `r` that the class algorithm returns on the underlying graph of `H′_j`, the vertex `r`, the
underlying graph of `A_j` and the weights `1` on the terminals of `J` and `0` elsewhere (`A_j[r, Z ∪ {r}]`); if
`p > k`, the union of the root paths to the terminals of `J`.

**Formalization Note.** The class algorithm reads graphs on `Fin N`; the vertices of `H′_j` are numbered by any
bijection `e`, and the numbering is a free choice of the run. -/
noncomputable def IsSeparator (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (par : Fin C.I.n → Fin C.I.n)
    (SW : Finset (Fin C.I.n)) : Prop := by
  classical
  exact
    (∃ t, C.I.K ∩ J.W = {t} ∧ SW = rootPathW C J cheap par t) ∨
    (¬ (∃ t, C.I.K ∩ J.W = {t}) ∧ C.p ≤ C.I.K.card ∧
      ∃ (N : ℕ) (e : Option (regionReach C J cheap) ≃ Fin N),
        let X : SepInput :=
          { N := N
            H := (underlyingH C J cheap).comap e.symm
            r := e none
            A := (underlyingA C J cheap par).comap e.symm
            μ := fun i => match e.symm i with
              | none => 0
              | some v => if v.1 ∈ C.I.K then 1 else 0 }
        SW = ((regionReach C J cheap).attach.filter fun v => (e (some v)).val ∈ C.Z X).biUnion
          fun v => rootPathW C J cheap par v.1) ∨
    (¬ (∃ t, C.I.K ∩ J.W = {t}) ∧ C.I.K.card < C.p ∧
      SW = (C.I.K ∩ J.W).biUnion fun t => rootPathW C J cheap par t)

/-- The children of `J` (App. C.3, step (6), p.40): one instance `(R ∪ (S_j ∖ {r}), C, K ∩ C)` for every weakly
connected component `C` of `H′_j − S_j` that contains a terminal, each listed once. Since `r ∈ S_j`, the components
are those of the vertices of `H′_j` outside `S_j`, joined by arcs of `G_{≤θ}` in either direction. -/
noncomputable def IsChildList (J : SInst C.I.n) (cheap : Fin C.I.n → Prop) (SW : Finset (Fin C.I.n))
    (ch : List (SInst C.I.n)) : Prop := by
  classical
  exact
    let D := regionReach C J cheap \ SW
    let G' : SimpleGraph (Fin C.I.n) :=
      SimpleGraph.fromRel fun a b => a ∈ D ∧ b ∈ D ∧ ArcLe C.I C.θ a b
    (∀ c ∈ ch, c.R = J.R ∪ SW) ∧ (ch.map SInst.W).Nodup ∧
      ∀ Wc : Finset (Fin C.I.n), Wc ∈ ch.map SInst.W ↔
        ∃ y ∈ D, Wc = D.filter (fun z => G'.Reachable y z) ∧ (C.I.K ∩ Wc).Nonempty

/-- The admissible weights of step (1) (App. C.3, p.40): with the future masses `m̄′` (after removing those of `J`)
and loads `ℓ`, `ω(u) = exp(ℓ(u)/σ + β m̄′(u))`, and `ω̃(u)` is a rational with `ω(u) ≤ ω̃(u) ≤ e^δ ω(u)` for every
`u ∈ R`. -/
def AdmissibleWeights (J : SInst C.I.n) (ℓ : Fin C.I.n → ℕ) (mbar' : Fin C.I.n → ℝ)
    (ω' : Fin C.I.n → ℚ) : Prop :=
  ∀ u ∈ J.R,
    Real.exp ((ℓ u : ℝ) / C.sigma + (C.beta : ℝ) * mbar' u) ≤ (ω' u : ℝ) ∧
    (ω' u : ℝ) ≤ Real.exp (C.delta : ℝ) * Real.exp ((ℓ u : ℝ) / C.sigma + (C.beta : ℝ) * mbar' u)

/-- The cheap G-tails of step (2) (App. C.3, p.40): with `Ω_j = Σ_{u ∈ R} ω̃(u) m_J(u)`, an entry arc with G-tail `u`
is cheap if `ω̃(u) ≤ Ω_j/ϵ`. -/
noncomputable def cheapTail (d : ℕ) (J : SInst C.I.n) (ω' : Fin C.I.n → ℚ) (u : Fin C.I.n) : Prop :=
  (ω' u : ℝ) ≤ (∑ w ∈ J.R, (ω' w : ℝ) * mass C d J w) / (C.eps : ℝ)

/-- **Processing one instance `J` of level `d`** (App. C.3, steps (1)–(6), pp.40; Algorithm 4, lines 12–23,
p.41), without failure: from loads `ℓ` and future masses `m̄`, it produces the new future masses `m̄′`, the new loads
`ℓ′`, the piece `pc` and the list `ch` of children, for some admissible weights `ω̃`, some breadth-first arborescence
`par` and some separator. -/
noncomputable def ProcStep (d : ℕ) (ℓ : Fin C.I.n → ℕ) (mbar : Fin C.I.n → ℝ) (J : SInst C.I.n)
    (ℓ' : Fin C.I.n → ℕ) (mbar' : Fin C.I.n → ℝ) (pc : Piece C.I.n) (ch : List (SInst C.I.n)) : Prop := by
  classical
  exact (mbar' = fun u => mbar u - mass C d J u) ∧
    ∃ ω' : Fin C.I.n → ℚ, AdmissibleWeights C J ℓ mbar' ω' ∧
      (∀ t ∈ C.I.K ∩ J.W, t ∈ regionReach C J (cheapTail C d J ω')) ∧
      ∃ par : Fin C.I.n → Fin C.I.n, IsBFSArb C J (cheapTail C d J ω') par ∧
        ∃ SW : Finset (Fin C.I.n), IsSeparator C J (cheapTail C d J ω') par SW ∧
          pc = { depth := d, R := J.R, SW := SW, par := par } ∧
          (ℓ' = fun u => ℓ u + if u ∈ J.R then (SW.filter fun v => par v = u).card else 0) ∧
          IsChildList C J (cheapTail C d J ω') SW ch

/-- **Failure at `J`** (App. C.3, step (3), p.40, Algorithm 4, line 17): for some admissible weights, some terminal of
`J` is not a vertex of `H′_j`. -/
noncomputable def ProcFail (d : ℕ) (ℓ : Fin C.I.n → ℕ) (mbar : Fin C.I.n → ℝ) (J : SInst C.I.n) : Prop :=
  ∃ ω' : Fin C.I.n → ℚ, AdmissibleWeights C J ℓ (fun u => mbar u - mass C d J u) ω' ∧
    ∃ t ∈ C.I.K ∩ J.W, t ∉ regionReach C J (cheapTail C d J (ω'))

/-- Processing the instances of level `d` one by one in the listed order (Algorithm 4, lines 11–24): the result is
`none` on failure, and otherwise the pieces and the children of the listed instances, in order. -/
inductive ProcList (d : ℕ) :
    (Fin C.I.n → ℕ) → (Fin C.I.n → ℝ) → List (SInst C.I.n) →
      Option (List (Piece C.I.n) × List (SInst C.I.n)) → Prop
  | nil (ℓ : Fin C.I.n → ℕ) (mbar : Fin C.I.n → ℝ) : ProcList d ℓ mbar [] (some ([], []))
  | fail (ℓ : Fin C.I.n → ℕ) (mbar : Fin C.I.n → ℝ) (J : SInst C.I.n) (rest : List (SInst C.I.n)) :
      ProcFail C d ℓ mbar J → ProcList d ℓ mbar (J :: rest) none
  | cons (ℓ : Fin C.I.n → ℕ) (mbar : Fin C.I.n → ℝ) (J : SInst C.I.n) (rest : List (SInst C.I.n))
      (ℓ' : Fin C.I.n → ℕ) (mbar' : Fin C.I.n → ℝ) (pc : Piece C.I.n) (ch : List (SInst C.I.n))
      (r : Option (List (Piece C.I.n) × List (SInst C.I.n))) :
      ProcStep C d ℓ mbar J ℓ' mbar' pc ch → ProcList d ℓ' mbar' rest r →
      ProcList d ℓ mbar (J :: rest) (r.map fun q => (pc :: q.1, ch ++ q.2))

/-- The initial future masses of a level (Algorithm 4, line 10): `m̄(u) = Σ_j m_{I_j}(u)`. -/
noncomputable def initMass (d : ℕ) (L : List (SInst C.I.n)) (u : Fin C.I.n) : ℝ :=
  (L.map fun J => mass C d J u).sum

/-- The levels `d, d + 1, …` of LEVELSEP (Algorithm 4, lines 8–26), starting from an ordering `L` of `I_d`: the result
is `none` on failure and otherwise the pieces of all instances of these levels. Every level starts with loads `0`;
the next level is processed in any order of the children. -/
inductive LevelsRun : ℕ → List (SInst C.I.n) → Option (List (Piece C.I.n)) → Prop
  | done (d : ℕ) : LevelsRun d [] (some [])
  | fail (d : ℕ) (L : List (SInst C.I.n)) :
      L ≠ [] → ProcList C d (fun _ => 0) (initMass C d L) L none → LevelsRun d L none
  | step (d : ℕ) (L : List (SInst C.I.n)) (pcs : List (Piece C.I.n)) (chs L' : List (SInst C.I.n))
      (r : Option (List (Piece C.I.n))) :
      L ≠ [] → ProcList C d (fun _ => 0) (initMass C d L) L (some (pcs, chs)) → L'.Perm chs →
      LevelsRun (d + 1) L' r → LevelsRun d L (r.map fun q => pcs ++ q)

/-- **A run of LEVELSEP(G, s, K, θ)** (Algorithm 4, lines 5–28, p.41; App. C.3, pp.39–40).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…).

Starting from level `0`, which consists of `I_0 = ({s}, V_{≤θ} ∖ {s}, K)`, the levels are processed one after the
other with the vector `x` of the context; the result is `none` (failure) or the list of the pieces of all instances,
each with its depth.

**Formalization Note.** Every free choice of the source is open: the order of the instances of a level, the
rational weights `ω̃ ∈ [ω, e^δ ω]`, the breadth-first arborescence, and the numbering of `H′_j` passed to the class
algorithm. -/
def LevelSepRun (r : Option (List (Piece C.I.n))) : Prop :=
  LevelsRun C 0 [{ R := {C.I.s}, W := VLe C.I C.θ \ {C.I.s} }] r

end DirTeleMC.Supplement


