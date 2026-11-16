-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
-- name    : StabPauli1264_Grouped_Supplement_Structure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:44:40.965221+00:00
-- url     : https://prove2.me/theorems/03790771-3dfb-449e-b288-7f78b8c9fb95
-- title:
--   Labels, commuting rank, frustration graph, shattering dimensions, graph and Ising windows
-- statement:
--   Let $M=(P_1,\ldots,P_m)$ be a window of signed Hermitian $n$-qubit Paulis (the base definition). Each $P_i$ equals $\pm X^{a}Z^{b}$ up to phase for a unique **symplectic label** $v_i=(a,b)\in\mathbb F_2^{n}\times\mathbb F_2^{n}$. A set $T\subseteq[m]$ has **independent labels** if $(v_i)_{i\in T}$ is linearly independent over $\mathbb F_2$. The **commuting rank** is
--
--   $$r(M)=\max\{|T| : T\text{ pairwise commuting with independent labels}\}.$$
--
--   The **frustration graph** $G_M$ on $[m]$ joins $i\ne j$ when $P_i,P_j$ do not commute. An **active dependency** is a nonempty pairwise commuting $D$ with $\sum_{i\in D}v_i=0$; $W_0$ consists of windows without active dependencies.
--
--   The **response class** is $F_M=\{f_\sigma\}$, $f_\sigma(i)=\operatorname{tr}(\sigma P_i)$ over pure stabilizer states $\sigma$ (valid tableaux), and $h_M(c)=\max_{f\in F_M}\langle c,f\rangle$. For a graph $H$ and weights $w$, $\alpha_w(H)$ is the largest $w$-weight of a graph independent set; $\operatorname{sgn}0=1$.
--
--   For $F\subseteq\mathbb R^{[m]}$: $T$ is **pseudo-shattered** if some thresholds $t$ realize every pattern of the strict events $f(i)>t_i$, $i\in T$; **exactly sign-shattered** if every $u\in\{\pm1\}^T$ equals $f|_T$ for some $f\in F$; **$\gamma$-fat-shattered** if some thresholds satisfy $u_i(f(i)-t_i)\ge\gamma$ for all $i\in T$ for every $u$ (weak margin). The **agreement class** consists of $a_f(i,s)=\mathbf 1[f(i)=s]$ on $[m]\times\{\pm1\}$. The dimensions $d_P,d_\pm,d_{\mathrm{fat}}(\cdot,\gamma),d_{\mathrm{VC}}$ are the largest sizes of shattered sets.
--
--   The **graph window** $M_H$ of a graph $H$ on $[m]$ has $n=m$ qubits and $P_v=X_v\prod_{u<v,\,uv\in E(H)}Z_u$ (Eq. (9)). An **Ising window** is $(Z_uZ_v)_{uv\in E}$ for a simple graph $([n],E)$ of maximum degree at most three, each edge listed once. The **independent-set mixture** of a law $D$ on subsets is $\rho_D=\mathbb E_{T\sim D}2^{-m}\prod_{v\in T}(I+P_v)$ (Eq. (10)); a **computational-basis mixture** is $\sum_xq(x)|x\rangle\langle x|$.
--
--   **Formalization Note** Labels live in $(\mathrm{Fin}\,n\to\mathbb Z/2)^2$. Maxima over finite nonempty families are written as finite suprema ($h_M$ and $\alpha_w$ as `sSup` of finite sets containing the empty choice). The agreement domain uses `Bool` with `true` for $+1$. Graph windows are characterized by `IsGraphWindow` ($n=m$ and $P_v$ as in Eq. (9) with sign $+$), and `graphWindow` builds them for $m\ge1$.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), §1.1 pp. 3–4; §2 pp. 5–8; Definition 5.1 p. 13; §6 p. 14; Eqs. (9)–(10) p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Complexity
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-! ### Symplectic labels, commuting rank, frustration graph, dependencies (pp. 4, 13) -/

/-- The symplectic label `v = (a, b) ∈ F₂ⁿ × F₂ⁿ`; signs and phases are forgotten. -/
abbrev Label (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- `X`-bit of a one-qubit Pauli (`X ↦ 1`, `Y ↦ 1`). -/
def xBit : Pauli → ZMod 2
  | .X => 1
  | .Y => 1
  | _ => 0

/-- `Z`-bit of a one-qubit Pauli (`Z ↦ 1`, `Y ↦ 1`). -/
def zBit : Pauli → ZMod 2
  | .Z => 1
  | .Y => 1
  | _ => 0

/-- The label of a Pauli string (`X^a Z^b` up to phase). -/
def label {n : ℕ} (P : PauliString n) : Label n :=
  (fun q => xBit (P.ops q), fun q => zBit (P.ops q))

/-- The observables indexed by `T` have labels linearly independent over `F₂`. -/
def IndepLabels {n m : ℕ} (M : Window n m) (T : Finset (Fin m)) : Prop :=
  LinearIndependent (ZMod 2) (fun i : T => label (M.observable i))

/-- The commuting rank `r(M)`: the largest size of a pairwise commuting set with independent
labels (p. 4). The empty set qualifies, so the maximum is over a nonempty finite family. -/
noncomputable def commutingRank {n m : ℕ} (M : Window n m) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter
    (fun T => IsContext M T ∧ IndepLabels M T)).sup Finset.card

/-- The frustration graph `G_M` on `[m]`: an edge `{i, j}` (`i ≠ j`) iff `P_i, P_j` do not commute
(commutation of matrices is symmetric, so `fromRel` adds nothing). -/
def frustrationGraph {n m : ℕ} (M : Window n m) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j => ¬ (M.observable i).Commute (M.observable j)

/-- An active dependency: a nonempty pairwise commuting `D` whose labels sum to zero. -/
def IsActiveDependency {n m : ℕ} (M : Window n m) (D : Finset (Fin m)) : Prop :=
  D.Nonempty ∧ IsContext M D ∧ ∑ i ∈ D, label (M.observable i) = 0

/-- `M` has no active dependencies (the class `W₀`). -/
def NoActiveDep {n m : ℕ} (M : Window n m) : Prop :=
  ∀ D : Finset (Fin m), ¬ IsActiveDependency M D

/-! ### Responses, support function and independent sets (pp. 5, 7, 13) -/

/-- The response class `F_M = {f_σ : σ a pure stabilizer state}` (valid tableaux only). -/
def responses {n m : ℕ} (M : Window n m) : Set (Fin m → ℝ) :=
  {f | ∃ T : Tableau n, IsValidTableau T ∧ f = response M T}

/-- The support function `h_M(c) = max_{f ∈ F_M} ⟨c, f⟩`, the supremum of a finite nonempty set. -/
noncomputable def supportFn {n m : ℕ} (M : Window n m) (c : Fin m → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ f ∈ responses M, r = ∑ i, c i * f i}

/-- `α_w(H)`: the largest `w`-weight of a graph independent set (the empty set included). -/
noncomputable def indepWeight {V : Type} [Fintype V] (H : SimpleGraph V) (w : V → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ T : Finset V, H.IsIndepSet (T : Set V) ∧ r = ∑ v ∈ T, w v}

/-- An inclusion-maximal graph independent set. -/
def IsMaximalIndep {V : Type} (H : SimpleGraph V) (T : Finset V) : Prop :=
  H.IsIndepSet (T : Set V) ∧ ∀ v, v ∉ T → ¬ H.IsIndepSet ((insert v T : Finset V) : Set V)

/-- `sgn` with the convention `sgn 0 = 1` (p. 12). -/
noncomputable def sgn (x : ℝ) : ℝ := if x < 0 then -1 else 1

/-! ### Shattering notions and dimensions on the finite domain `[m]` (pp. 5, 14) -/

/-- Pseudo-shattering: real thresholds realize every pattern of the strict events `f(i) > t_i`. -/
def PseudoShatters {m : ℕ} (F : Set (Fin m → ℝ)) (T : Finset (Fin m)) : Prop :=
  ∃ t : Fin m → ℝ, ∀ S ⊆ T, ∃ f ∈ F, ∀ i ∈ T, (t i < f i ↔ i ∈ S)

/-- Exact sign shattering: every sign pattern on `T` is the restriction of some `f ∈ F`. -/
def SignShatters {m : ℕ} (F : Set (Fin m → ℝ)) (T : Finset (Fin m)) : Prop :=
  ∀ S ⊆ T, ∃ f ∈ F, ∀ i ∈ T, f i = if i ∈ S then 1 else -1

/-- `γ`-fat shattering with the weak margin `u_i (f(i) − t_i) ≥ γ`. -/
def FatShatters {m : ℕ} (F : Set (Fin m → ℝ)) (γ : ℝ) (T : Finset (Fin m)) : Prop :=
  ∃ t : Fin m → ℝ, ∀ S ⊆ T, ∃ f ∈ F, ∀ i ∈ T,
    γ ≤ (if i ∈ S then (1 : ℝ) else -1) * (f i - t i)

/-- The outcome value of a point of `[m] × {±1}`: `true ↦ +1`, `false ↦ −1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- `B ⊆ [m] × {±1}` is shattered by the agreement class `A_F = {a_f(i,s) = 1[f(i) = s]}`. -/
def AgreementShatters {m : ℕ} (F : Set (Fin m → ℝ)) (B : Finset (Fin m × Bool)) : Prop :=
  ∀ S ⊆ B, ∃ f ∈ F, ∀ z ∈ B, (f z.1 = spin z.2 ↔ z ∈ S)

/-- Pseudo-dimension `d_P(F)`. -/
noncomputable def pseudoDim {m : ℕ} (F : Set (Fin m → ℝ)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter (PseudoShatters F)).sup Finset.card

/-- Exact sign-shattering dimension `d_±(F)`. -/
noncomputable def signDim {m : ℕ} (F : Set (Fin m → ℝ)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter (SignShatters F)).sup Finset.card

/-- Fat-shattering dimension `d_fat(F, γ)`. -/
noncomputable def fatDim {m : ℕ} (F : Set (Fin m → ℝ)) (γ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter (FatShatters F γ)).sup Finset.card

/-- VC dimension `d_VC(A_F)` of the agreement class on `[m] × {±1}`. -/
noncomputable def agreementVCDim {m : ℕ} (F : Set (Fin m → ℝ)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m × Bool))).filter (AgreementShatters F)).sup Finset.card

/-! ### Graph windows `M_H` (Eq. (9)), Ising windows, physical targets -/

/-- `P_v = X_v ∏_{u<v, uv∈E(H)} Z_u`, as an `n`-qubit string (qubits `≥ m` act trivially). -/
noncomputable def graphObs {n m : ℕ} (H : SimpleGraph (Fin m)) (v : Fin m) : PauliString n :=
  ⟨0, fun q => if h : q.val < m then
      (if q.val = v.val then .X else if q.val < v.val ∧ H.Adj ⟨q.val, h⟩ v then .Z else .I)
    else .I⟩

/-- `M` is the window `M_H` of Eq. (9): `n = m` and `P_v` is `graphObs H v` with sign `+`. -/
def IsGraphWindow {n m : ℕ} (M : Window n m) (H : SimpleGraph (Fin m)) : Prop :=
  n = m ∧ ∀ v, M.observable v = graphObs H v

/-- The `m`-qubit window `M_H` of a graph `H` on `[m]`, `m ≥ 1`. -/
noncomputable def graphWindow {m : ℕ} (H : SimpleGraph (Fin m)) (hm : 0 < m) : Window m m where
  observable := graphObs H
  hermitian _ := Or.inl rfl
  nonidentity v := ⟨v, by simp [graphObs]⟩
  distinct := by
    intro u v h
    by_contra hne
    have h' := congrFun h v
    simp only [graphObs] at h'
    split_ifs at h' <;> simp_all [Fin.ext_iff]
  nonempty := hm

/-- The uniform evaluation law on `[m]`, `m ≥ 1`. -/
noncomputable def uniformLaw (m : ℕ) (hm : 0 < m) : EvalLaw m where
  mass _ := 1 / (m : ℝ)
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- `Z_u Z_v` on `n` qubits, sign `+`. -/
def zzObs {n : ℕ} (u v : Fin n) : PauliString n :=
  ⟨0, fun q => if q = u ∨ q = v then .Z else .I⟩

/-- `M` is an Ising window `(Z_u Z_v)_{uv ∈ E}` of a simple graph `([n], E)` of maximum degree
at most three: its observables enumerate the edges, each exactly once (p. 8). -/
def IsIsingWindow {n m : ℕ} (M : Window n m) : Prop :=
  ∃ G : SimpleGraph (Fin n), (∀ v, (G.neighborSet v).ncard ≤ 3) ∧
    ∃ e : Fin m → Fin n × Fin n, (∀ i, G.Adj (e i).1 (e i).2) ∧
      (∀ u v, G.Adj u v → ∃ i, s((e i).1, (e i).2) = s(u, v)) ∧
      ∀ i, M.observable i = zzObs (e i).1 (e i).2

/-- A mixture `∑_x q(x) |x⟩⟨x|` of computational-basis states. -/
def IsBasisMixture {n : ℕ} (ρ : Mat n) : Prop :=
  ∃ q : Bits n → ℝ, (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧
    ρ = Matrix.diagonal (fun x => (q x : ℂ))

/-- `2^{-m} ∏_{v ∈ T} (I + P_v)` (ordered product along `[m]`). -/
noncomputable def setState {n m : ℕ} (M : Window n m) (T : Finset (Fin m)) : Mat n :=
  ((2 : ℂ) ^ m)⁻¹ • (List.ofFn fun v : Fin m => if v ∈ T then 1 + operator M v else 1).prod

/-- The independent-set mixture `ρ_D = E_{T∼D} 2^{-m} ∏_{v∈T} (I + P_v)` of Eq. (10). -/
noncomputable def setMixture {n m : ℕ} (M : Window n m)
    (D : OAI.ThorpCompatibility.Law (Finset (Fin m))) : Mat n :=
  ∑ T, (D.mass T : ℂ) • setState M T

/-- `D` is a law on graph independent sets of `H` with `Pr_{T∼D}[v ∈ T] = β` for every `v`. -/
def IsUniformIndepLaw {m : ℕ} (H : SimpleGraph (Fin m))
    (D : OAI.ThorpCompatibility.Law (Finset (Fin m))) (β : ℝ) : Prop :=
  (∀ T, D.mass T ≠ 0 → H.IsIndepSet (T : Set (Fin m))) ∧
  ∀ v, ∑ T ∈ Finset.univ.filter (fun T => v ∈ T), D.mass T = β

end StabPauli1264.Grouped.Supplement


