-- Prove2me | Definitions.Def_PinwheelDensity_ExactRange_checkRun
-- name    : PinwheelDensity_ExactRange_checkRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:18.513554+00:00
-- url     : https://prove2.me/theorems/4457bc70-5e58-42f8-af5e-715630a02784
-- title:
--   Cyclic words, split trees, absorption records and the explicit run checker
-- statement:
--   A **cyclic word** $w$ of length $N\ge1$ defines the schedule $t\mapsto w_{t\bmod N}$; symbols outside the task indices mean idle. For a task occurring at $t_0<\dots<t_{n-1}$, $n\ge1$, with $t_{j+n}=t_j+N$, the period $p/q$ passes the **gap test** of Lemma C.1 when $Nq\le np$ and $(t_k-t_j-1)q<(k-j)p$ for all $0\le j<k<2n$.
--
--   A **split tree** has leaves $E$ and $C(r,\pi,w)$ and inner nodes $S(i,x,T_1,T_2)$. It is **valid** for a box $(\ell,u)$ as follows. At $E$: $\sum1/u_i\ge\beta$. At $C$: $w$ passes the test for every task of $r>0$, and either $\sum1/u_i\ge\beta$ or $\mathrm{sort}(r)\le\pi(\mathrm{sort}\,L)$, where $L_i=\max(\ell_i,u_i/(1+\varepsilon u_i))$ and $\varepsilon=\beta-\sum1/u_i$. At $S$: $\ell_i<x<u_i$, with $T_1$ valid for $(\ell,u[i\mapsto x])$ and $T_2$ for $(\ell[i\mapsto x],u)$. In sorted mode each node first normalizes by $\ell_i\leftarrow\max_{j\le i}\ell_j$, $u_i\leftarrow\min_{j\ge i}u_j$, and is accepted outright if some $\ell_i>u_i$.
--
--   For **prefix absorption**, let $\tau_0<\dots<\tau_{f-1}$ be the free positions of $w$, and put $\hat\tau(j)=\tau_{j\bmod f}+\lfloor j/f\rfloor N$, $\mathrm{span}(b)=\max_{0\le j<f}(\hat\tau(j+b)-\hat\tau(j))$, $\kappa(a)=\#\{1\le b\le a:\mathrm{span}(b)\le a\}$, and
--   $$\rho^*(a^*)=\max\Big(\frac Nf,\ \max_{a^*\le a'<a^*+N}\frac{a'}{\kappa(a')}\Big).$$
--   An **absorption record** $(S,l,a_0,(w_s)_s)$ is valid when $S>0$, $\delta=B-D(S)>0$, and every enumerated case $s$, looked up by exact equality, has a word passing the test for $S+s$ such that, with $\rho=\delta-D(s)$, either $\rho=0$ or $\rho>0$, $f\ge1$, $\kappa(a^*)\ge1$ and $\rho\rho^*(a^*)\le5/6$ for $a^*=\max(a_0,\lceil1/\rho\rceil)$.
--
--   A **run** for $(m,B,\theta_0)$ has absorption records and stages $\theta_0,\theta_0+2,\dots,\Theta$, each listing certified cells and a residual list $R_\theta$. It is **accepted** when $1\le m$, $\theta_0\ge4$ is even, $0\le B\le1$, every case of the recomputed sets $K_{\theta_0}$ and $K_{\theta+2}=\bigcup_{c\in R_\theta}U_\theta^B(c)$ has a valid certificate at $\theta$ or lies in $R_\theta$, and $R_\Theta=\emptyset$.
--
--   This checker turns the infinite guarantee into a finite verification: the data supply witnesses only, and every case set is recomputed.
--
--   **Formalization Note** The checker is a total `Bool`-valued function with no assumption of soundness and no link to schedulability in its definition. It is written from the Appendices, not imported from the source's Lean development, and its tests are the plain quadratic ones rather than the source's running-minimum optimization. On the source's numbers it reproduces the worked example of Appendix C and the $l^*$ and word counts of all eleven records in Appendix F.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Appendix A, p. 10; Appendix C, pp. 13–14; Appendix D, pp. 15–16; Appendix E, p. 16 (same PDF pages)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_cellOf

namespace PinwheelDensity.ExactRange

/-- Positions `t₀ < ⋯ < tₙ₋₁` of the symbol `i` in the word `w` (Appendix C, p. 13). -/
def occurrences (w : List ℕ) (i : ℕ) : List ℕ :=
  (List.range w.length).filter fun t => w[t]? == some i

/-- The extended occurrences: `t_{j+n} = t_j + N` for `j < n`, where `N` is the word length. -/
def extOcc (w : List ℕ) (i j : ℕ) : ℕ :=
  let ts := occurrences w i
  if j < ts.length then ts.getD j 0 else ts.getD (j - ts.length) 0 + w.length

/-- The gap test of Lemma C.1, p. 13, for the task `i` and the period `p/q`: `n ≥ 1`, `N q ≤ n p`,
and `(t_k - t_j - 1) q < (k - j) p` for all `0 ≤ j < k < 2n`. -/
def gapTest (w : List ℕ) (i p q : ℕ) : Bool :=
  let n := (occurrences w i).length
  decide (1 ≤ n) && decide (w.length * q ≤ n * p) &&
    (List.range (2 * n)).all fun k => (List.range k).all fun j =>
      decide ((((extOcc w i k : ℤ) - (extOcc w i j : ℤ) - 1) * (q : ℤ)) <
        (((k : ℤ) - (j : ℤ)) * (p : ℤ)))

/-- A cyclic word of length `N ≥ 1` passes the test of Lemma C.1 for every task of the list `r`:
task `i` has period `rᵢ > 0`, written in lowest terms as `p/q`. The word defines the schedule
`t ↦ w[t mod N]`; symbols outside `0, …, |r| - 1` are idle days. -/
def wordServes (w : List ℕ) (r : List ℚ) : Bool :=
  decide (1 ≤ w.length) &&
    (List.range r.length).all fun i =>
      match r[i]? with
      | some a => decide (0 < a) && gapTest w i a.num.toNat a.den
      | none => false

/-- `fold_ij(v)` (Appendix A, p. 10): the sorted list obtained from `v` by deleting positions
`i, j` and adding `min(vᵢ, vⱼ)/2`; undefined if a position is out of range or `i = j`. -/
def pairFold (v : List ℚ) (i j : ℕ) : Option (List ℚ) :=
  if i = j then none
  else
    match v[i]?, v[j]? with
    | some a, some b =>
      some (sortQ (((v.eraseIdx (max i j)).eraseIdx (min i j)) ++ [min a b / 2]))
    | _, _ => none

/-- `π(v)` (Appendix A, p. 10): apply the folds of the sequence `π` in order. -/
def applyPairs : List (ℕ × ℕ) → List ℚ → Option (List ℚ)
  | [], v => some v
  | (i, j) :: π, v =>
    match pairFold v i j with
    | some v' => applyPairs π v'
    | none => none

/-- `∑ᵢ 1/uᵢ` for a list of upper bounds. -/
def sumRecip (u : List ℚ) : ℚ :=
  densityQ u

/-- Density tightening (Lemma C.2, p. 14): `Lᵢ = max(ℓᵢ, uᵢ/(1 + ε uᵢ))`, `ε = β - ∑ᵢ 1/uᵢ`. -/
def tighten (β : ℚ) (ℓ u : List ℚ) : List ℚ :=
  let ε := β - sumRecip u
  List.zipWith (fun a b => max a (b / (1 + ε * b))) ℓ u

/-- `ℓᵢ ← max_{j ≤ i} ℓⱼ` (sorted mode, Appendix C, p. 14). -/
def prefixMax : List ℚ → List ℚ
  | [] => []
  | x :: l => x :: prefixMax (l.map (max x))
termination_by l => l.length
decreasing_by simp

/-- `uᵢ ← min_{j ≥ i} uⱼ` (sorted mode, Appendix C, p. 14). -/
def suffixMin : List ℚ → List ℚ
  | [] => []
  | x :: l =>
    match suffixMin l with
    | [] => [x]
    | y :: t => min x y :: y :: t

/-- The box seen by a node: its normalization in sorted mode, the box itself otherwise. -/
def nodeLo (sortedMode : Bool) (ℓ : List ℚ) : List ℚ :=
  if sortedMode then prefixMax ℓ else ℓ

/-- See `nodeLo`. -/
def nodeUp (sortedMode : Bool) (u : List ℚ) : List ℚ :=
  if sortedMode then suffixMin u else u

/-- Sorted mode accepts a node outright if its normalized box has some `ℓᵢ > uᵢ`
(Appendix C, p. 14). In unsorted mode this never fires. -/
def acceptedOutright (sortedMode : Bool) (ℓ u : List ℚ) : Bool :=
  sortedMode &&
    (List.zipWith (fun a b => decide (b < a)) (nodeLo true ℓ) (nodeUp true u)).any id

/-- A split tree (Appendix C, p. 14): an empty leaf `E`, a certificate leaf `C(r, π, w)`, or an
inner node `S(i, x, T₁, T₂)`. -/
inductive SplitTree where
  | empty : SplitTree
  | cert (r : List ℚ) (π : List (ℕ × ℕ)) (w : List ℕ) : SplitTree
  | split (i : ℕ) (x : ℚ) (T₁ T₂ : SplitTree) : SplitTree

/-- Validity of a split tree for the box `(ℓ, u)` (Appendix C, p. 14). At `E`: `∑ 1/uᵢ ≥ β`. At `C`:
`w` passes the test of Lemma C.1 for every task of `r` (so `N ≥ 1` and `r > 0`), and either
`∑ 1/uᵢ ≥ β` or `sort(r) ≤ π(sort L)` with `π(sort L)` defined. At `S`: `ℓᵢ < x < uᵢ`, `T₁` is valid
for `(ℓ, u[i ↦ x])` and `T₂` for `(ℓ[i ↦ x], u)`. In sorted mode every node first replaces the box
by its normalization and is accepted outright if some `ℓᵢ > uᵢ`. -/
def checkTree (sortedMode : Bool) (β : ℚ) : SplitTree → List ℚ → List ℚ → Bool
  | .empty, ℓ, u =>
    acceptedOutright sortedMode ℓ u || decide (β ≤ sumRecip (nodeUp sortedMode u))
  | .cert r π w, ℓ, u =>
    acceptedOutright sortedMode ℓ u ||
      (wordServes w r &&
        (decide (β ≤ sumRecip (nodeUp sortedMode u)) ||
          match applyPairs π (sortQ (tighten β (nodeLo sortedMode ℓ) (nodeUp sortedMode u))) with
          | some v => leAll (sortQ r) v
          | none => false))
  | .split i x T₁ T₂, ℓ, u =>
    acceptedOutright sortedMode ℓ u ||
      match (nodeLo sortedMode ℓ)[i]?, (nodeUp sortedMode u)[i]? with
      | some a, some b =>
        decide (a < x) && decide (x < b) &&
          checkTree sortedMode β T₁ (nodeLo sortedMode ℓ) ((nodeUp sortedMode u).set i x) &&
          checkTree sortedMode β T₂ ((nodeLo sortedMode ℓ).set i x) (nodeUp sortedMode u)
      | _, _ => false

/-- Free positions `τ₀ < ⋯ < τ_{f-1}` of the word: those not used by the tasks `0, …, k - 1`
(Appendix D, p. 15). -/
def freePositions (w : List ℕ) (k : ℕ) : List ℕ :=
  (List.range w.length).filter fun t =>
    match w[t]? with
    | some a => decide (k ≤ a)
    | none => false

/-- `τ̂(j) = τ_{j mod f} + ⌊j/f⌋ N` for natural `j` (Appendix D, p. 15); used with `f ≥ 1`. -/
def tauHat (τ : List ℕ) (N j : ℕ) : ℕ :=
  τ.getD (j % τ.length) 0 + (j / τ.length) * N

/-- `span(b) = max_{0 ≤ j < f} (τ̂(j + b) - τ̂(j))` (Appendix D, p. 15). The subtraction is
exact because `τ̂` is increasing when `f ≥ 1`. -/
def span (τ : List ℕ) (N b : ℕ) : ℕ :=
  ((List.range τ.length).map fun j => tauHat τ N (j + b) - tauHat τ N j).foldr max 0

/-- `κ(a) = #{1 ≤ b ≤ a : span(b) ≤ a}` (Appendix D, p. 15). -/
def kappa (τ : List ℕ) (N a : ℕ) : ℕ :=
  ((List.range a).filter fun b => decide (span τ N (b + 1) ≤ a)).length

/-- `ρ*(a*) = max(N/f, max_{a* ≤ a' < a* + N} a'/κ(a'))` (Lemma D.1, p. 15), used for `κ(a*) ≥ 1`. -/
def rhoStar (τ : List ℕ) (N aStar : ℕ) : ℚ :=
  (List.range N).foldr
    (fun i acc => max acc (((aStar + i : ℕ) : ℚ) / (kappa τ N (aStar + i) : ℚ)))
    ((N : ℚ) / (τ.length : ℚ))

/-- The per-case condition of Proposition D.3, p. 16, for the case `s` with word `w`: `w` passes the
test of Lemma C.1 for the integer list `S + s` (tasks `0, …, |S| + |s| - 1` in this order), and with
`ρ = δ - D(s)` either `ρ = 0`, or `ρ > 0` and, with `a* = max(a₀, ⌈1/ρ⌉)`, the free positions of `w`
satisfy `f ≥ 1`, `κ(a*) ≥ 1` and `ρ ρ*(a*) ≤ 5/6`. A case with `ρ < 0` is rejected. -/
def absorbCaseOK (δ : ℚ) (S s w : List ℕ) (a₀ : ℕ) : Bool :=
  let ρ := δ - density s
  let aStar := max a₀ ⌈1 / ρ⌉₊
  let τ := freePositions w (S.length + s.length)
  wordServes w (toQ (S ++ s)) &&
    (decide (ρ = 0) ||
      (decide (0 < ρ) && decide (1 ≤ τ.length) && decide (1 ≤ kappa τ w.length aStar) &&
        decide (ρ * rhoStar τ w.length aStar ≤ 5 / 6)))

/-- The enumeration of cases of an absorption record (Appendix D, p. 16): the empty list and the
nondecreasing lists of at most `a₀ + 1` entries in `[l*, a₀)` with every prefix of density `≤ δ`. -/
def absEnum (δ : ℚ) (lStar a₀ : ℕ) : List (List ℕ) :=
  [] :: enumSorted (fun p => decide (density p ≤ δ)) lStar a₀ (a₀ + 1) []

/-- An absorption record `(S, l, a₀, (w_s)_s)` (Appendix D, p. 16). -/
structure AbsRecord where
  S : List ℕ
  l : ℕ
  a₀ : ℕ
  cases : List (List ℕ × List ℕ)

/-- Record validity (Appendix D, p. 16): `S` has positive entries, `δ = B - D(S) > 0`, and each
enumerated case, looked up by exact equality, satisfies the condition of Proposition D.3. -/
def checkAbsRecord (B : ℚ) (rec : AbsRecord) : Bool :=
  let δ := B - density rec.S
  let lStar := max rec.l ⌈1 / δ⌉₊
  rec.S.all (fun a => decide (0 < a)) && decide (0 < δ) &&
    (absEnum δ lStar rec.a₀).all fun s =>
      match rec.cases.lookup s with
      | some w => absorbCaseOK δ rec.S s w rec.a₀
      | none => false

/-- A certificate of a cell: a split tree with its mode flag, or the index of an absorption record. -/
inductive CellCert where
  | tree (sortedMode : Bool) (T : SplitTree) : CellCert
  | absorb (record : ℕ) : CellCert

/-- A stage of a run: cells with certificates, and the residual list `R_θ` (Appendix E, p. 16). -/
structure Stage where
  certs : List (List ℕ × CellCert)
  residual : List (List ℕ)

/-- Run data: absorption records, and the stages for `θ₀, θ₀ + 2, …` (Appendix E, p. 16). -/
structure Run where
  records : List AbsRecord
  stages : List Stage

/-- Parameters `(m, B, θ₀)`. -/
structure Params where
  m : ℕ
  B : ℚ
  θ₀ : ℕ

/-- Validity of a certificate for the cell `c` at stage `θ` (Appendix C, p. 14; Appendix D, p. 16):
a tree valid for the root box of `c` with `β = β_θ`, or an absorption record whose `S` is the list
of entries of `c` below `h`, with `l ≤ h`, that is valid. -/
def certValid (B : ℚ) (records : List AbsRecord) (θ : ℕ) (c : List ℕ) : CellCert → Bool
  | .tree sortedMode T => checkTree sortedMode (beta B θ) T (rootLo c) (rootUp θ c)
  | .absorb i =>
    match records[i]? with
    | some rec =>
      (rec.S == c.filter (fun x => x < θ / 2)) && decide (rec.l ≤ θ / 2) && checkAbsRecord B rec
    | none => false

/-- The stage walk (Appendix E, p. 16): at stage `θ` with recomputed case set `K`, every case has a
valid certificate at `θ` or lies in the residual `R_θ`; the next case set is
`K_{θ+2} = ⋃_{c ∈ R_θ} U_θ^B(c)`; the last stage must have an empty residual. An empty stage list is
rejected. Residuals are data and only enlarge the next case set. -/
def checkStages (B : ℚ) (records : List AbsRecord) : ℕ → List (List ℕ) → List Stage → Bool
  | _, _, [] => false
  | θ, K, st :: rest =>
    K.all (fun c =>
        st.certs.any (fun e => e.1 == c && certValid B records θ c e.2) ||
          st.residual.contains c) &&
      match rest with
      | [] => st.residual.isEmpty
      | _ :: _ => checkStages B records (θ + 2) (st.residual.flatMap (unfoldCell B θ)) rest

/-- Parameter conditions (Appendix E, p. 16): `1 ≤ m`, `θ₀ ≥ 4` even, `0 ≤ B ≤ 1`. -/
def paramsOK (P : Params) : Bool :=
  decide (1 ≤ P.m) && decide (4 ≤ P.θ₀) && decide (P.θ₀ % 2 = 0) && decide (0 ≤ P.B) &&
    decide (P.B ≤ 1)

/-- Acceptance of a run (Appendix E, p. 16): the parameter conditions hold, and the stage walk
accepts starting from the recomputed initial case set `K_θ₀`. The data supply only witnesses. -/
def checkRun (P : Params) (d : Run) : Bool :=
  paramsOK P && checkStages P.B d.records P.θ₀ (initCases P.m P.B P.θ₀) d.stages

end PinwheelDensity.ExactRange


