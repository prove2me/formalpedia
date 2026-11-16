-- Prove2me | Definitions.Def_DetCCHard_Supplement_SrcData
-- name    : DetCCHard_Supplement_SrcData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:54:35.15347+00:00
-- url     : https://prove2.me/theorems/f786e9c4-f31a-4033-a6d3-69dbce9ff2c5
-- title:
--   The source construction $R \mapsto R^+$ of Definitions 6.2 and 8.3, parametrized by tuple lists
-- statement:
--   Fix a base matrix $R : X \times Y \to \{0,1\}$ with positive normalized rational weights $\mu_X, \mu_Y$, a source graph $G = (V, E)$, a dyadic number of bins $s \ge 4$, $q_1 = s - 2$, and $q_2 = q_0 2^t$ with $q_0 = \mathrm{pow}_2(4s|E|)$. Items are $I = [4s] \times (V \sqcup [s-3])$ with activity indicators $v_i(\alpha)$, and $\pi_\alpha(i)$ numbers the items active at $\alpha$ in a fixed order. The construction takes four lists: a **Γ-list** of lists $\gamma \in Y^{2s-1}$, a list of **tails** $\xi \in Y^{s+1}$, a list of **template labels** $z \in J^{q_2}$ with $J = [q_1] \times X$, and a list of **bin tuples** $(j_1, \dots, j_s) \in J_2^s$ with $J_2 = [q_2] \times \Gamma$. Then
--   $$
--   A(\gamma, (r, u)) = R(u, \gamma_r), \qquad R_{\mathrm{temp}}(z, (\alpha, \gamma)) = A(\gamma, z_\alpha).
--   $$
--   The raw matrix $B_{\mathrm{raw}}$ has template rows $(p, z) \in [s] \times S$ (total weight $\lambda = 255/256$) and item rows $(i, u) \in I \times X$ (vertex rows and auxiliary rows each of total weight $\mu/2$, $\mu = 1/256$), and columns $Z = (\xi, j_1, \dots, j_s)$, $j_p = (\alpha_p, \gamma_p)$, from two families: $\Omega$ (a tail label and a bin-tuple label, product weights, total $\lambda$) and $\mathcal D = \{(\mathrm{tail}(\gamma), j, \dots, j) : j = (\alpha, \gamma) \in J_2\}$ (weights induced from $J_2$, total $\mu$). Its entries are
--   $$
--   B_{\mathrm{raw}}((p, z), Z) = R_{\mathrm{temp}}(z, j_p), \qquad
--   B_{\mathrm{raw}}((i, u), Z) = \begin{cases} R(u, \xi_{\pi_\alpha(i)}) & \alpha_1 = \dots = \alpha_s = \alpha,\ v_i(\alpha) = 1,\\ R(u, \xi_{s+1}) & \text{otherwise.}\end{cases}
--   $$
--   Finally $N = B_{\mathrm{raw}}^{\mathsf T}$, $N_{\mathrm{ref}} = N[\Omega, K]$ with normalized $\Omega$ weights, $U = I_w(N)$ on a list of $w$-tuples of columns of $N$, $W = U^{\mathsf T}$, and $R^+ = (I_Q(W))^{\mathsf T}$ on an outer list of $Q$-tuples of columns of $W$. The $(H3)$ list of $U$ combines three label sequences (type/bin/item labels, base labels, template labels) coordinatewise.
--
--   The full-product construction of Definition 6.2 takes every list to be a full product; the explicit construction of Definition 8.3 takes exactly 8192-wise independent lists. Both are instances of this one parametrized construction.
--
--   **Formalization Note** The $2s - 1$ positions of $\gamma$ are indexed by $[q_1] \sqcup [s+1]$ (template positions, then tail positions); blocks and positions are $0$-based; the item order is an arbitrary injection into $\mathbb N$; the two column families keep distinct labels.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 6.2, pp.19–20, and Definition 8.3, pp.35–36

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_Item
import Definitions.Def_DetCCHard_WMat
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_Supplement_RawList

namespace DetCCHard.Supplement

open DetCCHard

/-- The weight `λ = 255/256` of the template rows and of the column family `Ω`
(Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Definition 6.2,
p.19). -/
def lam : ℚ := 255 / 256

/-- The weight `µ = 1/256` of the item rows and of the column family `D` (Definition 6.2, p.19). -/
def mu : ℚ := 1 / 256

/-- The **positions of a list** `γ ∈ Γ = Y^{2s−1}` (Definition 6.2, p.19): the `q₁ = s − 2`
template positions (`Sum.inl r`) followed by the `s + 1` tail positions (`Sum.inr k`), since
`q₁ + s + 1 = 2s − 1`.

**Formalization Note** The `2s − 1` positions are indexed by `Fin (s − 2) ⊕ Fin (s + 1)` instead of
`[2s − 1]`: position `r ≤ q₁` is `Sum.inl (r − 1)` and position `q₁ + k` is `Sum.inr (k − 1)`. This is
a bijection for `s ≥ 2`, so tuples, weights and exact independence are unchanged. -/
abbrev GPos (s : ℕ) : Type := Fin (s - 2) ⊕ Fin (s + 1)

/-- The number of indices `q₂ = q₀ · 2^t`, a dyadic multiple of `q₀ = pow2(4s|E|)`
(Definition 6.2, p.19; published `baseCoordCount`). -/
def q2 (G : SrcGraph) (s t : ℕ) : ℕ := baseCoordCount G s * 2 ^ t

/-- The weights on `J = [q₁] × X` (Definition 6.2, p.19): the position `r ∈ [q₁]` is uniform and
`u` has the base row weight, `μ_J(r, u) = μX(u)/(s − 2)`. -/
noncomputable def jWt (R : WMat) (s : ℕ) : Fin (s - 2) × R.X → ℚ :=
  fun j => R.μX j.2 / ((s - 2 : ℕ) : ℚ)

/-- The weights on `J₂ = [q₂] × Γ` (Definition 6.2, p.19, and Definition 8.3, p.35): the index
`α ∈ [q₂]` is uniform and the list label `γ` has the weight of the Γ-list, `μ_{J₂}(α, γ) = ν(γ)/q₂`. -/
noncomputable def j2Wt {Y : Type} {s : ℕ} (TΓ : RawList Y (GPos s)) (q : ℕ) : Fin q × TΓ.L → ℚ :=
  fun j => TΓ.ν j.2 / (q : ℚ)

/-- The **tail list of a Γ-list** (Definition 8.3, p.35–36: "the weights induced on the tail by
`Γ_g`"): the same labels and weights, each decoding to the tail `tail(γ) = (γ_{q₁+1}, …, γ_{2s−1})`
of its list. Labels with equal tails stay separate, each with its own weight. -/
def RawList.tailList {Y : Type} {s : ℕ} (T : RawList Y (GPos s)) : RawList Y (Fin (s + 1)) where
  L := T.L
  ν := T.ν
  z := fun ℓ k => T.z ℓ (Sum.inr k)

/-- The **data of the source construction**, parametrized by tuple lists (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Definition 6.2, pp.19–20, and
Definition 8.3, pp.35–36): the base matrix `R` with its positive normalized rational weights, the
source graph `G`, the dyadic number of bins `s`, the exponent `t` with `q₂ = q₀·2^t`, a fixed order
on the items `I` (used to number the active items), and four lists:
* `TΓ`, the **Γ-list** of lists `γ ∈ Y^{2s−1}` (marginal `μY`);
* `TΩ`, the list of **tails** `ξ ∈ Y^{s+1}` of the `Ω`-inputs;
* `TS`, the list of **template labels** `z ∈ J^{q₂}`, `J = [q₁] × X` (marginal `jWt`);
* `TB`, the list of **bin tuples** `(j₁, …, j_s) ∈ J₂^s`, `J₂ = [q₂] × Γ` (marginal `j2Wt`).

The full-product construction of Definition 6.2 takes every list to be the full product
(`SrcData.full`); the explicit construction of Definition 8.3 takes exactly 8192-wise independent
lists, with `TΩ` the tail list of `TΓ`.

**Formalization Note** The order on `I` is an injection into `ℕ`; the paper fixes an unspecified
order, so statements quantify over all of them. -/
structure SrcData where
  /-- the base matrix with its input weights -/
  R : WMat
  /-- the source graph -/
  G : SrcGraph
  /-- the number of bins (a power of two, at least `4`, in every statement) -/
  s : ℕ
  /-- the exponent with `q₂ = q₀ · 2^t` -/
  t : ℕ
  /-- the fixed order on the items -/
  ord : Item s G.n ↪ ℕ
  /-- the Γ-list -/
  TΓ : RawList R.Y (GPos s)
  /-- the list of tails of the Ω-inputs -/
  TΩ : RawList R.Y (Fin (s + 1))
  /-- the list of template labels -/
  TS : RawList (Fin (s - 2) × R.X) (Fin (q2 G s t))
  /-- the list of bin tuples of the Ω-inputs -/
  TB : RawList (Fin (q2 G s t) × TΓ.L) (Fin s)

namespace SrcData

variable (D : SrcData)

/-- `q₂` of the construction. -/
abbrev q : ℕ := q2 D.G D.s D.t

/-- The labels of the column family `Ω` of `B_raw` (rows of `N`): a tail label and a bin-tuple
label. -/
abbrev Omega : Type := D.TΩ.L × D.TB.L

/-- The **rows of `N`** (columns of `B_raw`, Definition 6.2, p.20): the `Ω`-inputs (`Sum.inl`) and
the `D`-inputs (`Sum.inr`), one for each `j = (α, γ) ∈ J₂`. The two families have distinct labels. -/
abbrev NRow : Type := D.Omega ⊕ (Fin D.q × D.TΓ.L)

/-- The **columns of `N`** (rows `K` of `B_raw`, Definition 6.2, p.19):
`K = ([s] × S) ⊔ (I × X)`, the template rows `(p, z)` and the item rows `(i, u)`. -/
abbrev KRow : Type := (Fin D.s × D.TS.L) ⊕ (Item D.s D.G.n × D.R.X)

/-- The **first template interlace** `A(γ, (r, u)) = R(u, γ_r)` (Definition 6.2, p.19), with rows
the Γ-labels and columns `J = [q₁] × X`. -/
def A : D.TΓ.L → Fin (D.s - 2) × D.R.X → Bool :=
  fun γ j => D.R.entry j.2 (D.TΓ.z γ (Sum.inl j.1))

/-- The **second template interlace** `R_temp(z, (α, γ)) = A(γ, z_α)` (Definition 6.2, p.19), with
rows the template labels `S` and columns `J₂ = [q₂] × Γ`. -/
def Rtemp : D.TS.L → Fin D.q × D.TΓ.L → Bool :=
  fun z j => D.A j.2 (D.TS.z z j.1)

/-- The shared list `ξ ∈ Y^{s+1}` of a column of `B_raw` (Definition 6.2, pp.19–20): the decoded
tail label for an `Ω`-input, `tail(γ)` for the `D`-input `(α, γ)`. -/
def xi : D.NRow → Fin (D.s + 1) → D.R.Y
  | Sum.inl ω => D.TΩ.z ω.1
  | Sum.inr j => fun k => D.TΓ.z j.2 (Sum.inr k)

/-- The bin tuple `(j₁, …, j_s) ∈ J₂^s` of a column of `B_raw` (Definition 6.2, pp.19–20): the
decoded bin-tuple label for an `Ω`-input, `(j, …, j)` for the `D`-input `j`. -/
def bins : D.NRow → Fin D.s → Fin D.q × D.TΓ.L
  | Sum.inl ω => D.TB.z ω.2
  | Sum.inr j => fun _ => j

/-- The **position `π_α(i)`** of an item among the items active at index `α` (Definition 6.2, p.19:
"the map numbering the at most `s − 1` active items `1, 2, …` in a fixed order on `I`").

**Formalization Note** Positions are `0`-based: the first active item reads `ξ` at index `0`. The
value is the number of active items preceding `i` in the order, capped at `s` so that it is always a
position of `ξ`; for an active item of a source graph it is at most `s − 2`, so the cap never acts
where the value is used. -/
noncomputable def pos (α : Fin D.q) (i : Item D.s D.G.n) : Fin (D.s + 1) :=
  ⟨min (Nat.card {i' : Item D.s D.G.n // active D.G D.s D.t i' α ∧ D.ord i' < D.ord i}) D.s,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

open Classical in
/-- The **raw matrix `B_raw`** (Definition 6.2, p.19): for a column `Z = (ξ, j₁, …, j_s)` with
`j_p = (α_p, γ_p)`,
`B_raw((p, z), Z) = R_temp(z, j_p)`, and
`B_raw((i, u), Z) = R(u, ξ_{π_α(i)})` if `α₁ = ⋯ = α_s = α` and `v_i(α) = 1`, else `R(u, ξ_{s+1})`.

**Formalization Note** `v_i(α) = 1` is the published `active`; `ξ_{s+1}` is the last position
(`Fin.last s`, `0`-based). -/
noncomputable def Braw : D.KRow → D.NRow → Bool
  | Sum.inl (p, z), c => D.Rtemp z (D.bins c p)
  | Sum.inr (i, u), c =>
      if h : ∃ α : Fin D.q, (∀ p, (D.bins c p).1 = α) ∧ active D.G D.s D.t i α then
        D.R.entry u (D.xi c (D.pos (Classical.choose h) i))
      else D.R.entry u (D.xi c (Fin.last D.s))

/-- The **source matrix** `N = B_rawᵀ` (Definition 6.2, p.20): rows the `Ω`- and `D`-inputs,
columns `K`. -/
noncomputable def N : D.NRow → D.KRow → Bool := fun c r => D.Braw r c

/-- The **weights on `K`** (columns of `N`, rows of `B_raw`; Definition 6.2, p.19): template rows
total `λ`, vertex rows and auxiliary rows each total `µ/2`; within each type the bin or item is
uniform and `z` or `u` has the weights of `S` or `X`. -/
noncomputable def KWt : D.KRow → ℚ
  | Sum.inl (_, z) => lam * (1 / (D.s : ℚ)) * D.TS.ν z
  | Sum.inr ((_, Sum.inl _), u) => mu / 2 * (1 / ((4 * D.s * D.G.n : ℕ) : ℚ)) * D.R.μX u
  | Sum.inr ((_, Sum.inr _), u) => mu / 2 * (1 / ((4 * D.s * (D.s - 3) : ℕ) : ℚ)) * D.R.μX u

/-- The **weights on the rows of `N`** (Definition 6.2, p.20): the family `Ω` has weight `λ`, with
the product of the tail weight and the bin-tuple weight; the family `D` has weight `µ`, with the
weights induced from `J₂`. -/
noncomputable def NWt : D.NRow → ℚ
  | Sum.inl ω => lam * (D.TΩ.ν ω.1 * D.TB.ν ω.2)
  | Sum.inr j => mu * (D.TΓ.ν j.2 / (D.q : ℚ))

/-- The **reference matrix** `N_ref = N[Ω, K]` (Definition 6.2, p.20): `N` restricted to the
`Ω`-rows. -/
noncomputable def Nref : D.Omega → D.KRow → Bool := fun ω r => D.N (Sum.inl ω) r

/-- The row weights of `N_ref`: the weights of `N` on `Ω`, normalized (Definition 6.2, p.20). -/
noncomputable def NrefWt : D.Omega → ℚ :=
  fun ω => D.NWt (Sum.inl ω) / ∑ ω' : D.Omega, D.NWt (Sum.inl ω')

/-- The **type/bin/item labels** of the `(H3)` decomposition (§6.5, p.27, and Definition 8.3, p.36):
a template type with its bin `p` (`Sum.inl p`) or an item (`Sum.inr i`). -/
abbrev TypeLab : Type := Fin D.s ⊕ Item D.s D.G.n

/-- The weights on type/bin/item labels induced by the row weights of `B_raw` (§6.5, p.27):
`λ/s` for each bin, `(µ/2)/(4sn)` for each vertex item, `(µ/2)/(4s(s − 3))` for each auxiliary
item. -/
noncomputable def typeWt : D.TypeLab → ℚ
  | Sum.inl _ => lam * (1 / (D.s : ℚ))
  | Sum.inr (_, Sum.inl _) => mu / 2 * (1 / ((4 * D.s * D.G.n : ℕ) : ℚ))
  | Sum.inr (_, Sum.inr _) => mu / 2 * (1 / ((4 * D.s * (D.s - 3) : ℕ) : ℚ))

/-- The **combined tuple list of `(H3)`** (§6.5, p.27, and Definition 8.3, p.36): from three lists
of `w`-tuples (type/bin/item labels, base labels in `X`, template labels in `S`), the list whose
labels are the triples of labels with product weights, decoding at copy `i` to the template row
`(p, z_i)` if the first sequence gives a template type with bin `p`, and to the item row `(a, u_i)`
if it gives item `a`. -/
def combineH3 {w : ℕ} (T1 : RawList D.TypeLab (Fin w)) (T2 : RawList D.R.X (Fin w))
    (T3 : RawList D.TS.L (Fin w)) : RawList D.KRow (Fin w) where
  L := T1.L × T2.L × T3.L
  ν := fun ℓ => T1.ν ℓ.1 * T2.ν ℓ.2.1 * T3.ν ℓ.2.2
  z := fun ℓ i =>
    match T1.z ℓ.1 i with
    | Sum.inl p => Sum.inl (p, T3.z ℓ.2.2 i)
    | Sum.inr a => Sum.inr (a, T2.z ℓ.2.1 i)

/-- The **first further interlace** `U = I_w(N)` on a tuple list `TU` of `w`-tuples of columns of
`N` (Definition 6.2, p.20, and Definition 8.3, p.36): rows `(i, a) ∈ [w] × (Ω ⊔ D)`, one column per
label, entry `N(a, z_i(ℓ))`. Its row weights are `NWt(a)/w` (published `interlaceRowWt`), its
column weights `TU.ν`. -/
noncomputable def U {w : ℕ} (TU : RawList D.KRow (Fin w)) : Fin w × D.NRow → TU.L → Bool :=
  TU.interlace D.N

/-- `W = Uᵀ` (Definition 6.2, p.20): rows the labels of `TU` (weights `TU.ν`), columns
`[w] × (Ω ⊔ D)` (weights `NWt(a)/w`). -/
noncomputable def W {w : ℕ} (TU : RawList D.KRow (Fin w)) : TU.L → Fin w × D.NRow → Bool :=
  fun ℓ r => D.U TU r ℓ

/-- The **output** `R⁺ = (I_Q(W))ᵀ` on an outer list `TQ` of `Q`-tuples of columns of `W`
(Definition 6.2, p.20, and Definition 8.3, p.36): rows the labels of `TQ` (weights `TQ.ν`),
columns `(i, ℓ) ∈ [Q] × TU.L` (weights `TU.ν(ℓ)/Q`), entry `W(ℓ, z_i(ℓ_Q))`. -/
noncomputable def Rplus {w Q : ℕ} (TU : RawList D.KRow (Fin w))
    (TQ : RawList (Fin w × D.NRow) (Fin Q)) : TQ.L → Fin Q × TU.L → Bool :=
  fun ℓ r => D.W TU r.2 (TQ.z ℓ r.1)

/-- The **full-product construction** of Definition 6.2 (pp.19–20): every list is the full product
with product weights: `Γ = Y^{2s−1}` with `μY`, the tails `Y^{s+1}` with `μY`, `S = J^{q₂}` with
the `J` weights and the bin tuples `J₂^s` with the `J₂` weights. -/
noncomputable def full (R : WMat) (G : SrcGraph) (s t : ℕ) (ord : Item s G.n ↪ ℕ) : SrcData where
  R := R
  G := G
  s := s
  t := t
  ord := ord
  TΓ := RawList.full R.μY (GPos s)
  TΩ := RawList.full R.μY (Fin (s + 1))
  TS := RawList.full (jWt R s) (Fin (q2 G s t))
  TB := RawList.full (j2Wt (RawList.full R.μY (GPos s)) (q2 G s t)) (Fin s)

/-- The full product of `w`-tuples of columns of `N` with the product of the `K` weights: the list
of the full-product interlace `U = I_w(N)` (Definition 6.2, p.20). -/
noncomputable def fullU (w : ℕ) : RawList D.KRow (Fin w) := RawList.full D.KWt (Fin w)

/-- The full product of `Q`-tuples of columns of `W` with the product of `W`'s column weights: the
outer list of the full-product interlace `R⁺ = (I_Q(W))ᵀ` (Definition 6.2, p.20). -/
noncomputable def fullQ (w Q : ℕ) : RawList (Fin w × D.NRow) (Fin Q) :=
  RawList.full (interlaceRowWt D.NWt w) (Fin Q)

end SrcData

end DetCCHard.Supplement


