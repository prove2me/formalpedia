-- Prove2me | Definitions.Def_NoisyOWMPC_releaseHalf
-- name    : NoisyOWMPC_releaseHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:51:43.335162+00:00
-- url     : https://prove2.me/theorems/35c74790-7401-49c8-8e1a-f1f8aa965c86
-- title:
--   The release test of Construction 5.11 (protocol half)
-- statement:
--   Let $t=2dM^8$ ($d=|\mathcal X|$), $n_{\mathrm{rel}}=Mt$ and $a_t=\lceil t^{11/20}\rceil$. For a signed row $\theta=((x_s,\epsilon_s))_{s\in[t]}$ and a query $w\in\mathcal Y_i^t$, $\mathrm{Check}_{i,\theta}(w)=1$ when every $(x_s,w_s)$ is supported and $|n_{x,z}(w)-N_xC_i(z\mid x)|\le a_t$ for all $x,z$. With
--   $$B_{i,\theta}(w)=\sum_{s=1}^t\epsilon_s\beta_i(x_s,w_s),\qquad h_{i,\theta}(w)=\mathrm{Check}_{i,\theta}(w)\,\mathbf 1[B_{i,\theta}(w)\ge0],$$
--   the **release test** is $Q_\Theta(w)=\mathbf 1[\sum_{j=1}^M h_{i,\theta_j}(w_j)>M/2]$. $\mathrm{Gen}_{\mathrm{rel},i}$ samples $M$ independent rows, each uniform among words with exactly $t/(2d)$ copies of every $(x,\epsilon)\in\mathcal X\times\{-1,1\}$; $\mathrm{Word}_{\mathrm{rel},i}$ outputs the entries $x_{j,s}$ in row order.
--
--   **Formalization Note** The channel probability in the consistency check is $\mathrm{apx}$; supports use the true channel (§5 Conventions, p.21).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5.2.2, p.26; Construction 5.11, p.26

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves
import Definitions.Def_NoisyOWMPC_symEnc

namespace NoisyOWMPC

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The release row length `t = t_rel = 2dM⁸`, `d = |X|` (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), §5.2.2 Parameters, p.26). -/
def tRel (X : Type) [Fintype X] (M : ℕ → ℕ) (lam : ℕ) : ℕ := 2 * Fintype.card X * M lam ^ 8

/-- The release channel-input length `n_rel = Mt = 2dM⁹` (p.26). -/
def nRel (X : Type) [Fintype X] (M : ℕ → ℕ) (lam : ℕ) : ℕ := M lam * tRel X M lam

/-- The consistency tolerance `a_t = ⌈t^{11/20}⌉` (p.26). -/
noncomputable def aTol (t : ℕ) : ℕ := ⌈(t : ℝ) ^ ((11 : ℝ) / 20)⌉₊

open Classical in
/-- A signed row `θ = ((x_s, ε_s))_{s ∈ [t]}` is **balanced** (Construction 5.11, `Gen_rel,i`,
p.26: "words containing exactly `t/(2d)` copies of every `(x, ε) ∈ X × {−1, 1}`"), with
`t/(2d) = M⁸`; the sign `ε_s = +1` is `true`. -/
def RelBalanced (Mv : ℕ) {t : ℕ} (θ : Fin t → X × Bool) : Prop :=
  ∀ a e, (Finset.univ.filter fun s => θ s = (a, e)).card = Mv ^ 8

/-- A release state `Θ = (θ_j)_{j ∈ [M]}` of balanced rows. -/
abbrev RelSec (X : Type) [Fintype X] (M : ℕ → ℕ) (lam : ℕ) : Type :=
  Fin (M lam) → {θ : Fin (tRel X M lam) → X × Bool // RelBalanced (M lam) θ}

open Classical in
/-- The **channel-consistency check** `Check_{i,θ}(w)` (§5.2.2, p.26): every `(x_s, w_s)` is
supported, `C_i(w_s | x_s) > 0`, and `|n_{x,z}(w) − N_x C_i(z | x)| ≤ a_t` for all `x ∈ X`,
`z ∈ Y_i`, with `N_x = |{s : x_s = x}|`, `n_{x,z}(w) = |{s : x_s = x, w_s = z}|` and the
probability in the comparison replaced by its rational upper approximation `apx`. -/
def relCheck (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ) (i : Fin k) (lam : ℕ) {t : ℕ}
    (θ : Fin t → X × Bool) (w : Fin t → Y i) : Prop :=
  (∀ s, 0 < (C i).P (θ s).1 (w s)) ∧
  ∀ a z, |((Finset.univ.filter fun s => (θ s).1 = a ∧ w s = z).card : ℚ) -
    ((Finset.univ.filter fun s => (θ s).1 = a).card : ℚ) * apx lam i a z| ≤ (aTol t : ℚ)

/-- The **signed score** `B_{i,θ}(w) = ∑_{s=1}^t ε_s β_i(x_s, w_s)` (Construction 5.11, p.26). -/
def relScore {Yi : Type} (β : X → Yi → Bool) {t : ℕ} (θ : Fin t → X × Bool) (w : Fin t → Yi) : ℤ :=
  ∑ s, (if (θ s).2 then (1 : ℤ) else -1) * (if β (θ s).1 (w s) then 1 else 0)

open Classical in
/-- The **release test** `Q_Θ(w) = 1[∑_{j=1}^M h_{i,θ_j}(w_j) > M/2]` with the row indicator
`h_{i,θ}(w) = Check_{i,θ}(w) 1[B_{i,θ}(w) ≥ 0]` (Construction 5.11, p.26); `w_j` is the `j`th
length-`t` row of the query. -/
noncomputable def relQ (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (i : Fin k) (M : ℕ → ℕ) (lam : ℕ) (Θ : RelSec X M lam)
    (w : Fin (nRel X M lam) → Y i) : Bool :=
  decide (M lam < 2 * (Finset.univ.filter fun j : Fin (M lam) =>
    relCheck C apx i lam (Θ j).1 (fun s => w (finProdFinEquiv (j, s))) ∧
      0 ≤ relScore (β i) (Θ j).1 (fun s => w (finProdFinEquiv (j, s)))).card)

open Classical in
/-- **Construction 5.11 (Release test), protocol half** (STOC 2027 submission (manuscript sha256
3a9569fa…), p.26): `Gen_rel,i(1^λ)` samples `M` independent uniform balanced signed rows,
`Word_rel,i(Θ)` outputs the entries `x_{j,s}` in row order, and `Q_Θ` is `relQ`.

**Formalization Note** Rows are `Fin t → X × Bool`; the state is uniform on `M`-tuples of balanced
rows; its encoding lists, row by row, each symbol's code and its sign bit. -/
noncomputable def releaseHalf (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (M : ℕ → ℕ) (i : Fin k) : TestHalf X (Y i) (nRel X M) where
  Sec := RelSec X M
  genW lam := unifW _
  enc lam Θ := (List.ofFn fun j : Fin (M lam) => (List.ofFn fun s : Fin (tRel X M lam) =>
    symEnc X (symWidth X) ((Θ j).1 s).1 ++ [((Θ j).1 s).2]).flatten).flatten
  word lam Θ p := ((Θ (finProdFinEquiv.symm p).1).1 (finProdFinEquiv.symm p).2).1
  test lam Θ w := relQ C apx β i M lam Θ w

end NoisyOWMPC


