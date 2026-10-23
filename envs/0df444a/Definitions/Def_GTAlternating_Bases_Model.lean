-- Prove2me | Definitions.Def_GTAlternating_Bases_Model
-- name    : GTAlternating_Bases_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:30.894813+00:00
-- url     : https://prove2.me/theorems/02d8538b-2100-4c56-94bf-6983dbbc5e1c
-- title:
--   §§2–6, pp. 3–14 — Young's orthogonal form, the associator φ_λ of (9), A_k-isotypic components, labels Θ̃(n), paths S̃(α) and the vectors u_α of Definition 2
-- statement:
--   This module sets up the objects of Geetha and Prasad's comparison of Gelfand–Tsetlin bases for the symmetric group $S_n$ and the alternating group $A_n$.
--
--   1. **Young's orthogonal form** (pp. 4–5). For a partition $\lambda$ of $n$, $V_\lambda$ is the complex vector space with basis $\{v_T \mid T \in \mathcal T(\lambda)\}$ indexed by the standard Young tableaux of shape $\lambda$. For the simple transposition $s_i = (i, i+1)$, let $i$ lie in row $j$, column $k$ of $T$ and $i+1$ in row $j'$, column $k'$, and put $r = (k'-j') - (k-j)$. Then
--   $$\rho_\lambda(s_i) v_T = \begin{cases} v_T & j = j',\\ -v_T & k = k',\\ r^{-1} v_T + \sqrt{1 - r^{-2}}\, v_{s_iT} & \text{otherwise,}\end{cases}$$
--   where $s_iT$ interchanges $i$ and $i+1$ in $T$ (formula (2)).
--   2. **The embedding (4)** (p. 6). For $\mu \in \lambda^{\downarrow}$ (the diagram of $\mu$ is that of $\lambda$ with one box removed), $v_T \mapsto v_{T^\lambda}$, where $T^\lambda$ is $T$ with $n$ written in the box $\lambda \setminus \mu$.
--   3. **The associator** (pp. 7–9). $d(\lambda)$ is the number of diagonal boxes of $\lambda$. For a self-conjugate $\lambda$ the reference tableau $T_\lambda$ is chosen through the self-conjugate cover containing $\lambda$: if the last diagonal box of $\lambda$ is removable, $T_\lambda$ is the row superstandard tableau of $\mu = \lambda$ minus that box, with $n$ added on the diagonal; otherwise $T_\lambda$ is the row superstandard tableau of $\lambda$ (rows read left to right, top to bottom, give $1,\dots,n$). With $w_T$ the permutation taking each entry of $T_\lambda$ to the entry of $T$ in the same box and $T'$ the conjugate tableau,
--   $$\varphi_\lambda(v_T) = i^{(n-d(\lambda))/2}\,\epsilon(w_T)\, v_{T'} \qquad (9),$$
--   and $V_\lambda^{\pm}$ are the $\pm 1$ eigenspaces of $\varphi_\lambda$. For an arbitrary partition $\lambda$, an arbitrary reference tableau $T_0$ of shape $\lambda$ and an arbitrary scalar $c_0$, the module also defines the map (7) of p. 8, $v_T \mapsto c_0\,\epsilon(w_T)\,v_{T'} \in V_{\lambda'}$, with $w_T$ taken relative to $T_0$.
--   4. **$A_k$-equivariance and isotypic subspaces.** A linear map $f : V_\mu \to V_\lambda$ is $A_k$-equivariant if it intertwines $\rho(s_i)\rho(s_j)$ for all $1 \le i, j \le k-1$. The $A_k$-isotypic subspace of $V_\lambda$ of type $W \le V_\mu$ is the sum of the images $f(W)$ over all $A_k$-equivariant $f$. A subspace is an irreducible $A_k$-representation if it is nonzero, stable under these products, and has no stable subspace other than $0$ and itself.
--   5. **Labels and paths** (pp. 10–12). $\tilde\Theta(n)$ consists of the non-self-conjugate partitions $\lambda$ of $n$ and the symbols $\lambda^{\pm}$ for self-conjugate $\lambda$; $V_\alpha$ is $V_\lambda$ or $V_\lambda^{\pm}$. $\alpha \sim \beta$ iff $\alpha = \beta$ or both are non-self-conjugate and $\beta = \alpha'$. $\beta \in \alpha^\dagger$ iff the partition of $\beta$ is obtained from that of $\alpha$ by removing one box and, when both are self-conjugate, the signs agree (cases (1)–(5), p. 12). $\tilde{\mathcal S}(\alpha)$ is the set of sequences $(\alpha^{(2)},\dots,\alpha^{(n)})$ with $\alpha^{(i)} \in (\alpha^{(i+1)})^\dagger$ and $\alpha^{(n)} = \alpha$.
--   6. **Definition 2** (pp. 13–14). $u_{(2)} = v_{[1\,2]}$, $u_{(1^2)} = v_{[1/2]}$, and recursively, with $\underline\alpha^* = (\alpha^{(2)},\dots,\alpha^{(n-1)})$ and $x = u^\lambda_{\underline\alpha^*}$ the image of $u_{\underline\alpha^*}$ under (4): $u_{\underline\alpha} = x \pm \varphi_\lambda(x)$ if $\alpha = \lambda^\pm$ and $\alpha^{(n-1)}$ is non-self-conjugate (11); $u_{\underline\alpha} = x$ otherwise ((12), (13)).
--   7. **Gelfand–Tsetlin vectors.** For a path $\gamma$, $V_\gamma$ is the set of vectors of $V_\alpha$ lying, for every $k = 2,\dots,n-1$, in the $A_k$-isotypic subspace of type $V_{\alpha^{(k)}}$. A Gelfand–Tsetlin basis vector for $\gamma$ is a nonzero vector of $V_\gamma$. $W \sqsubset V$ (Theorem 2) means that the $A_{n-1}$-isotypic subspace of type $W$ in $V$ is nonzero. The count $r$ of Theorem 3 is the number of indices $i$ with $\alpha^{(i)}$ self-conjugate and $\alpha^{(i+1)}$ not.
--
--   These are the objects every statement of the mission is about. The Gelfand–Tsetlin notion is intrinsic: it is defined through isotypic components, never through the explicit vectors $u_{\underline\alpha}$.
--
--   **Formalization Note.** `lam` stands for $\lambda$ and `mu` for $\mu$. Tableaux are the published `YoungTableau` of `QAlgorithms_Papers_Independent_Renew46_P26`: labels are $0,\dots,n-1$ (the paper's entry $i$ is label $i-1$), boxes are 0-based (row, column), so `sigma lam i` is the paper's $\rho_\lambda(s_{i+1})$ and the diagonal box $(d,d)$ is $(d-1,d-1)$. $V_\lambda$ is the space of finitely supported functions on $\mathcal T(\lambda)$. Young's formulas are **operators**, one per simple transposition, not a group representation: that they define a representation of $S_n$ is the cited [5, Theorem 2.1], not a result of the paper. Consequently $A_k$-equivariance is stated on the generators $s_is_j$ ($i,j\le k-1$) of $A_k$, which is equivalent to equivariance under $A_k$ once Young's formulas define a representation. Constructions that need a validity proof (the swapped tableau, $T^\lambda$, $T'$, the base tableau of size 2) use a classical choice with junk value $0$, which is never reached on valid inputs; `embed mu lam` is $0$ unless $\mu \in \lambda^\downarrow$, and `phi lam` is $0$ unless $\lambda$ is self-conjugate. The exponent $(n-d(\lambda))/2$ is natural-number division, exact for self-conjugate $\lambda$. `sigma lam i` is the identity for $i+1 \ge n$ (never used). Paths are stored top-down as lists $[\alpha^{(n-1)},\dots,\alpha^{(2)}]$ below $\alpha^{(n)}$.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, pp. 3–14, §§2–6: (2) p. 5, (3)–(4) p. 6, (5) p. 6, (7)–(9) pp. 8–9, Definition 1 p. 8, Θ̃(n) p. 10, † and S̃(α) p. 12, Definition 2 pp. 13–14

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

namespace GTAlternating.Bases

noncomputable section

open Classical
open QAlgorithms.Papers.Independent.Renew46.P26

/-- `SYT lam` = 𝒯(λ): standard Young tableaux of shape `lam` (p. 4). Labels are
`0, …, n-1` (the paper's entries `1, …, n`), `n = |lam|`; the box of label `k` is `T.1.1 k`. -/
def SYT (lam : YoungDiagram) := {T : YoungTableau lam.cells.card // tableauShape T = lam}

/-- `V lam` = V_λ, the complex vector space with Young's orthogonal basis `{v_T | T ∈ 𝒯(λ)}` (p. 4). -/
abbrev V (lam : YoungDiagram) := SYT lam →₀ ℂ

/-- The basis vector `v_T`. -/
def vT {lam : YoungDiagram} (T : SYT lam) : V lam := Finsupp.single T 1

/-- The box carrying label `k` in a tableau (junk `(0,0)` for `k ≥ n`; only used for `k < n`). -/
def boxOf {n : ℕ} (T : YoungTableau n) (k : ℕ) : ℕ × ℕ :=
  if h : k < n then T.1 ⟨k, h⟩ else (0, 0)

/-- `v_{s_{i+1} T}` (0-based `i`): the basis vector of the tableau obtained from `T` by
interchanging the labels `i` and `i+1`; `0` if that is not a standard tableau (never the case in
the third line of Young's formulas (2)). -/
def swapVec {lam : YoungDiagram} (T : SYT lam) (i : ℕ) : V lam :=
  if h : ∃ U : SYT lam, ∀ k, boxOf U.1 k =
      boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k) then
    Finsupp.single h.choose 1
  else 0

/-- Young's orthogonal form (2), p. 5: the operator `ρ_λ(s_{i+1})` on `V_λ` (0-based `i`, so it
interchanges the labels `i` and `i+1`, the paper's entries `i+1` and `i+2`). With `r` the content
of label `i+1` minus the content of label `i`:
`v_T ↦ v_T` (same row), `-v_T` (same column), `r⁻¹ v_T + √(1 - r⁻²) v_{s T}` otherwise.
For `i + 1 ≥ n` (no such simple transposition) it is the identity; such `i` are never used. -/
def sigma (lam : YoungDiagram) (i : ℕ) : Module.End ℂ (V lam) :=
  Finsupp.linearCombination ℂ (fun T : SYT lam =>
    if i + 1 < lam.cells.card then
      (let a := boxOf T.1 i
       let b := boxOf T.1 (i + 1)
       if a.1 = b.1 then vT T
       else if a.2 = b.2 then -vT T
       else
         let r : ℤ := boxContent b - boxContent a
         ((r : ℂ)⁻¹) • vT T + ((Real.sqrt (1 - 1 / (r : ℝ) ^ 2) : ℝ) : ℂ) • swapVec T i)
    else vT T)

/-- The embedding (3)–(4), p. 6: for `µ ∈ λ↓`, `v_T ↦ v_{T^λ}`, where `T^λ` puts the new label
`n-1` (the paper's entry `n`) in the box `λ ∖ µ`. The zero map unless `µ ∈ λ↓`. -/
def embed (mu lam : YoungDiagram) : V mu →ₗ[ℂ] V lam :=
  Finsupp.linearCombination ℂ (fun T : SYT mu =>
    if h : YoungEdge mu lam ∧
        ∃ U : SYT lam, ∀ k, k < mu.cells.card → boxOf U.1 k = boxOf T.1 k then
      Finsupp.single h.2.choose 1
    else 0)

/-- `v_{T'}` placed in `V mu`: the conjugate tableau `T'` (reflection of `T` about the principal
diagonal, p. 6) when it is a standard tableau of shape `mu`; `0` otherwise. Used with
`mu = lam.transpose` (Lemma 2) and, for self-conjugate `lam`, with `mu = lam`. -/
def conjInto (mu : YoungDiagram) {lam : YoungDiagram} (T : SYT lam) : V mu :=
  if h : mu.cells.card = lam.cells.card ∧
      ∃ U : SYT mu, ∀ k, k < lam.cells.card → boxOf U.1 k = (boxOf T.1 k).swap then
    Finsupp.single h.2.choose 1
  else 0

/-- `d(λ) = max{i | i ≤ λ_i}`, the number of boxes on the principal diagonal (p. 8). -/
def diagLen (lam : YoungDiagram) : ℕ := (lam.cells.filter (fun b => b.1 = b.2)).card

/-- The cells of a diagram in row-major (reading) order: rows top to bottom, each left to right. -/
def cellsLex (lam : YoungDiagram) : List (ℕ × ℕ) :=
  ((lam.cells.image toLex).sort (· ≤ ·)).map ofLex

/-- The last diagonal cell `(d-1, d-1)` (0-based; the paper's `(d, d)`) is removable, i.e. `λ`
is the larger partition of its self-conjugate cover (Definition 1, p. 8). -/
def lastDiagRemovable (lam : YoungDiagram) : Prop :=
  0 < diagLen lam ∧ (diagLen lam - 1, diagLen lam) ∉ lam.cells ∧
    (diagLen lam, diagLen lam - 1) ∉ lam.cells

/-- `refBox lam k`: the box of label `k` in the reference tableau `T_λ` of pp. 8–9. If `λ` is the
smaller partition of its self-conjugate cover, `T_λ` is the row superstandard tableau (labels in
reading order). If `λ` is the larger one, `µ = λ ∖ {(d-1,d-1)}` and `T_λ = T_µ^λ`: the row
superstandard tableau of `µ` with the last label `n-1` on the diagonal box `(d-1,d-1)`. -/
def refBox (lam : YoungDiagram) (k : ℕ) : ℕ × ℕ :=
  if lastDiagRemovable lam then
    (if k + 1 = lam.cells.card then (diagLen lam - 1, diagLen lam - 1)
     else ((cellsLex lam).filter (fun b => b ≠ (diagLen lam - 1, diagLen lam - 1))).getD k (0, 0))
  else (cellsLex lam).getD k (0, 0)

/-- `ϵ(w_T)` (p. 7): the sign of the permutation `w_T` taking each entry of `T_λ` to the entry of
`T` in the same box, computed as `(-1)^{#inversions}`. -/
def signW {lam : YoungDiagram} (T : SYT lam) : ℂ :=
  (-1 : ℂ) ^ ((Finset.univ.filter (fun p : Fin lam.cells.card × Fin lam.cells.card =>
    p.1 < p.2 ∧ labelAt T.1 (refBox lam p.1) > labelAt T.1 (refBox lam p.2))).card)

/-- `ϵ(w_T)` relative to an arbitrary reference tableau `T0` (p. 7: "for each partition λ fix a
standard tableau T_λ"): the sign of the permutation taking each entry of `T0` to the entry of `T`
in the same box, computed as `(-1)^{#inversions}`. -/
def signWRel {lam : YoungDiagram} (T0 T : SYT lam) : ℂ :=
  (-1 : ℂ) ^ ((Finset.univ.filter (fun p : Fin lam.cells.card × Fin lam.cells.card =>
    p.1 < p.2 ∧ labelAt T.1 (T0.1.1 p.1) > labelAt T.1 (T0.1.1 p.2))).card)

/-- The linear map `V_λ → V_λ′` of (7), p. 8, for any partition `λ`: `v_T ↦ c_T v_{T′}` with
`c_T = c_{T_λ} ϵ(w_T)`, where the reference tableau is `T0` and `c_{T_λ} = c0` is arbitrary. -/
def assocRel {lam : YoungDiagram} (T0 : SYT lam) (c0 : ℂ) : V lam →ₗ[ℂ] V lam.transpose :=
  Finsupp.linearCombination ℂ (fun T : SYT lam => (c0 * signWRel T0 T) • conjInto lam.transpose T)

/-- The associator φ_λ normalised by (9), p. 9: `φ_λ(v_T) = i^{(n - d(λ))/2} ϵ(w_T) v_{T'}`.
Meaningful for self-conjugate `λ` (then `T'` has shape `λ` and `n - d(λ)` is even); for
`λ ≠ λ'` it is the zero map, and it is never used there. -/
def phi (lam : YoungDiagram) : Module.End ℂ (V lam) :=
  Finsupp.linearCombination ℂ (fun T : SYT lam =>
    (Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW T) • conjInto lam T)

/-- `V_λ^+` (`plus = true`) and `V_λ^-` (`plus = false`): the `+1` and `-1` eigenspaces of `φ_λ`
(p. 9). -/
def Vpm (lam : YoungDiagram) (plus : Bool) : Submodule ℂ (V lam) :=
  LinearMap.ker (phi lam - (if plus then (1 : ℂ) else -1) • (1 : Module.End ℂ (V lam)))

/-- A linear map `V_µ → V_λ` is `A_k`-equivariant: it intertwines the products
`ρ(s_{i+1}) ρ(s_{j+1})` for all `0 ≤ i, j` with `i + 1, j + 1 < k`, i.e. the paper's `s_i s_j` with
`1 ≤ i, j ≤ k - 1`; these products generate `A_k`. -/
def IsAltEquivariant (k : ℕ) {mu lam : YoungDiagram} (f : V mu →ₗ[ℂ] V lam) : Prop :=
  ∀ i j, i + 1 < k → j + 1 < k → f ∘ₗ (sigma mu i * sigma mu j) = (sigma lam i * sigma lam j) ∘ₗ f

/-- A subspace `W ≤ V_λ` is an irreducible representation of `A_k`: it is nonzero, stable under
every `ρ(s_{i+1}) ρ(s_{j+1})` with `i + 1, j + 1 < k`, and has no stable subspace other than `0`
and `W`. -/
def IsAltIrreducible (k : ℕ) {lam : YoungDiagram} (W : Submodule ℂ (V lam)) : Prop :=
  W ≠ ⊥ ∧
  (∀ i j, i + 1 < k → j + 1 < k → ∀ x ∈ W, sigma lam i (sigma lam j x) ∈ W) ∧
  ∀ U : Submodule ℂ (V lam), U ≤ W →
    (∀ i j, i + 1 < k → j + 1 < k → ∀ x ∈ U, sigma lam i (sigma lam j x) ∈ U) →
    U = ⊥ ∨ U = W

/-- The `A_k`-isotypic subspace of `V_λ` of type `W ≤ V_µ`: the sum of the images `f(W)` over all
`A_k`-equivariant linear maps `f : V_µ → V_λ`. -/
def Iso (k : ℕ) {mu : YoungDiagram} (W : Submodule ℂ (V mu)) (lam : YoungDiagram) :
    Submodule ℂ (V lam) :=
  ⨆ (f : V mu →ₗ[ℂ] V lam) (_ : IsAltEquivariant k f), W.map f

/-- Elements of `Θ̃(n)` (p. 10): a non-self-conjugate partition `λ`, or `λ^±` for a
self-conjugate `λ` (`plus = true` for `λ^+`). -/
inductive Label
  | nsc (lam : YoungDiagram) (h : lam.transpose ≠ lam)
  | sc (lam : YoungDiagram) (h : lam.transpose = lam) (plus : Bool)

namespace Label

/-- The underlying partition of a label. -/
def shape : Label → YoungDiagram
  | nsc lam _ => lam
  | sc lam _ _ => lam

/-- `n` for a label in `Θ̃(n)`. -/
def size (a : Label) : ℕ := a.shape.cells.card

/-- Whether the label is of the form `λ^±`. -/
def isSc : Label → Bool
  | nsc _ _ => false
  | sc _ _ _ => true

/-- `V_α` as a subspace of `V_{shape α}`: all of `V_λ` for non-self-conjugate `λ`, `V_λ^±` for
`λ^±` (p. 10). -/
def space : (a : Label) → Submodule ℂ (V a.shape)
  | nsc _ _ => ⊤
  | sc lam _ plus => Vpm lam plus

/-- `α ∼ β` (pp. 10–12): `α = β`, or both are non-self-conjugate partitions and `β = α'`. -/
def Equiv (a b : Label) : Prop :=
  a = b ∨ (a.isSc = false ∧ b.isSc = false ∧ b.shape = a.shape.transpose)

end Label

/-- `β ∈ α†` (p. 12): `β`'s partition is obtained from `α`'s by removing one box, and if both are
self-conjugate the signs agree. This is exactly the five cases (1)–(5) of p. 12. -/
def Dagger (a b : Label) : Prop :=
  YoungEdge b.shape a.shape ∧
    match a, b with
    | .sc _ _ s, .sc _ _ t => s = t
    | _, _ => True

/-- `IsPath a p`: the sequence `α̲ = (α^{(2)}, …, α^{(n)})` with `α^{(n)} = a` lies in `S̃(a)`
(p. 12). It is stored top-down: `p = [α^{(n-1)}, …, α^{(2)}]`, and `α^{(2)} ∈ Θ̃(2)`. -/
def IsPath : Label → List Label → Prop
  | a, [] => a.size = 2
  | a, b :: rest => Dagger a b ∧ IsPath b rest

/-- The vectors `u_α̲` of Definition 2 (pp. 13–14), for the path `(a :: p)` stored top-down.
(10): for `|a| = 2`, the basis vector of the unique standard tableau of shape `(2)` or `(1²)`.
(11): `a = λ^±`, `α^{(n-1)}` non-self-conjugate: `u = x ± φ_λ(x)` with `x = u_{α̲*}^λ`.
(12), (13): otherwise `u = u_{α̲*}^λ`, the image of `u_{α̲*}` under the embedding (4). -/
def uVec : (a : Label) → List Label → V a.shape
  | a, [] =>
      if h : a.size = 2 ∧ Nonempty (SYT a.shape) then Finsupp.single (Classical.choice h.2) 1
      else 0
  | a, b :: rest =>
      match a, b with
      | .sc lam _ s, .nsc mu hmu =>
          embed mu lam (uVec (.nsc mu hmu) rest) +
            (if s then (1 : ℂ) else -1) • phi lam (embed mu lam (uVec (.nsc mu hmu) rest))
      | a, b => embed b.shape a.shape (uVec b rest)

/-- The Gelfand–Tsetlin subspace `V_γ` of `V_α` for the path `(a :: p)`: the vectors of `V_α`
lying, for every level `k = 2, …, n-1`, in the `A_k`-isotypic subspace of type `V_{α^{(k)}}`. -/
def GTLine (a : Label) (p : List Label) : Submodule ℂ (V a.shape) :=
  a.space ⊓ ⨅ b ∈ p, Iso b.size b.space a.shape

/-- `x` is a Gelfand–Tsetlin basis vector of `V_α` corresponding to the path `(a :: p)`:
a nonzero vector of `V_γ`. -/
def IsGTVector (a : Label) (p : List Label) (x : V a.shape) : Prop :=
  x ≠ 0 ∧ x ∈ GTLine a p

/-- `W ⊏ V` (Theorem 2, p. 10): `V_β` occurs in the restriction of `V_α` to `A_{n-1}`. -/
def Occurs (b a : Label) : Prop :=
  Iso (a.size - 1) b.space a.shape ⊓ a.space ≠ ⊥

/-- The branching count `r` of Theorem 3 (p. 12) for a path stored top-down: the number of
consecutive pairs `(α^{(i+1)}, α^{(i)})` with `α^{(i)}` self-conjugate and `α^{(i+1)}` not. -/
def branchCount : List Label → ℕ
  | x :: y :: rest =>
      (if x.isSc = false ∧ y.isSc = true then 1 else 0) + branchCount (y :: rest)
  | _ => 0

end

end GTAlternating.Bases


