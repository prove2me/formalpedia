-- Prove2me | Definitions.Def_NoisyOWMPC_releaseTest
-- name    : NoisyOWMPC_releaseTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:59:31.50913+00:00
-- url     : https://prove2.me/theorems/9086ca70-c890-45dc-bd47-d983e384f197
-- title:
--   Construction 5.11: the release test with its proof-side algorithms
-- statement:
--   Fix receiver $i$, rows of length $t=2dM^8$, the margin $b_t=\lceil t^{2/5}\rceil$ and the expander $\mathcal G_{\mathrm{rel}}$ with $\ell_{\mathrm{rel}}=M^8$, $G=\lceil M^{2/5}\rceil$. Construction 5.11 is:
--   1. $\mathrm{Gen}$, $\mathrm{Word}$, $Q_\Theta$ as in the protocol half;
--   2. $\mathrm{SampleSt}$: sample $(\Theta^0,D)$ from the honest experiment, record $H=Q_{\Theta^0}(D_i)$, the signed weights $J_j=J(\theta^0_j,D_j)$ of (5.11), the labels (5.12)
--   $$\Phi_j=\begin{cases}A,&h_{i,\theta^0_j}(D_{i,j})=1,\\ R,&\mathrm{Check}=1\text{ and }B\le-b_t,\\ F,&\text{otherwise},\end{cases}$$
--   and $T_j(\zeta)=\pi_{j,\zeta}\theta^0_j$ for independent uniform permutations preserving the equal-$D_j$ position sets; return $\mathrm{st}=(D,H,J,\Phi,T)$ with $\mathrm{obs}(\mathrm{st})=D$, $H(\mathrm{st})=H$;
--   3. $\mathrm{Recons}(\mathrm{st},\sigma)$: $\theta_j=T_j(\gamma_j(\sigma))$;
--   4. $\mathrm{Rec}(\mathrm{st},w)$: empty if $H=1$; otherwise $L^{\mathrm{raw}}_j=\{\zeta:h_{i,T_j(\zeta)}(w_j)=1\}$ if $\Phi_j=R$ and $\emptyset$ otherwise, truncated above $\ell_{\mathrm{rel}}$; return $\mathrm{Rec}_{\mathcal G_{\mathrm{rel}}}(\bigcup_j\{j\}\times L_j)$.
--
--   **Formalization Note** The expander is the graph of a family as in Corollary A.8; labels $A,R,F$ are $0,1,2$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5.2.2, pp.26–27; Construction 5.11, pp.26–27

import Mathlib
import Definitions.Def_NoisyOWMPC_releaseHalf
import Definitions.Def_NoisyOWMPC_accessTest

namespace NoisyOWMPC

open LaconicBarrier KarpLiptonOM

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]

open Classical in
/-- Permuting positions preserves the number of positions carrying a given value. -/
theorem card_filter_permRow {α : Type} {t : ℕ} (π : Equiv.Perm (Fin t)) (θ : Fin t → α) (p : α) :
    (Finset.univ.filter fun s => θ (π.symm s) = p).card =
      (Finset.univ.filter fun s => θ s = p).card := by
  refine Finset.card_bij (fun s _ => π.symm s) ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢; exact hs
  · intro s _ s' _ hss; exact π.symm.injective hss
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨π s, by simpa using hs, by simp⟩

/-- A permutation of the positions keeps a signed row balanced (Construction 5.11, p.27: "each
signed pair `(x, ε)` moves together"; the permuted row has the same counts). -/
theorem relBalanced_permRow {Mv t : ℕ} (π : Equiv.Perm (Fin t)) (θ : Fin t → X × Bool)
    (h : RelBalanced Mv θ) : RelBalanced Mv (permRow π θ) := by
  intro a e
  rw [← h a e]
  unfold permRow
  convert card_filter_permRow π θ (a, e)

/-- The rejection margin `b_t = ⌈t^{2/5}⌉` (§5.2.2 Parameters, p.26). -/
noncomputable def bMar (t : ℕ) : ℕ := ⌈(t : ℝ) ^ ((2 : ℝ) / 5)⌉₊

/-- The release expander `G_rel`: the layered `(M ℓ_rel, G, L_out)`-list-recoverable graph of the
family `Gr` with `M` layers, `ℓ_rel = M⁸` and `G = ⌈M^{2/5}⌉` (p.26). -/
noncomputable def gRel (Gr : (M ℓ G : ℕ) → LayeredGraph M) (M : ℕ → ℕ) (lam : ℕ) :
    LayeredGraph (M lam) :=
  Gr (M lam) (M lam ^ 8) (gPar (M lam))

open Classical in
/-- The **row label** (5.12) (p.27), `0 = A`, `1 = R`, `2 = F`:
`Φ_{i,θ}(v) = A` if `h_{i,θ}(v) = 1`; `R` if `Check_{i,θ}(v) = 1` and `B_{i,θ}(v) ≤ −b_t`; `F`
otherwise. -/
noncomputable def rowLabel (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (i : Fin k) (lam : ℕ) {t : ℕ} (θ : Fin t → X × Bool)
    (v : Fin t → Y i) : Fin 3 :=
  if relCheck C apx i lam θ v ∧ 0 ≤ relScore (β i) θ v then 0
  else if relCheck C apx i lam θ v ∧ relScore (β i) θ v ≤ -(bMar t : ℤ) then 1
  else 2

open Classical in
/-- The **signed weight** (5.11) (p.26): `J_{a,e,z}(θ, d) = |{s : x_s = a, ε_s = e, d_s = z}|` for
a signed row `θ` and a full observation row `d ∈ Y_allᵗ`. -/
noncomputable def signedWeight {t : ℕ} (θ : Fin t → X × Bool) (d : Fin t → ∀ j, Y j) :
    X → Bool → (∀ j, Y j) → Fin (t + 1) :=
  fun a e z => ⟨(Finset.univ.filter fun s => θ s = (a, e) ∧ d s = z).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- A **sampler state of the release test** `st = (D, H, J, Φ, T)` (Construction 5.11,
`SampleSt_rel,i`, p.27): the full observation `D`, the honest bit `H`, the signed weights `J_j`, the
labels `Φ_j` and the candidate rows `T_j(ζ)` (balanced signed rows), `j ∈ [M]`, `ζ ∈ H_rel`. -/
abbrev RelSt (X : Type) [Fintype X] (Y : Fin k → Type) (M : ℕ → ℕ) (lam h : ℕ) : Type :=
  (Fin (nRel X M lam) → ∀ j, Y j) × Bool × (Fin (M lam) → X → Bool → (∀ j, Y j) → Fin (tRel X M lam + 1)) ×
    (Fin (M lam) → Fin 3) × (Fin (M lam) → Fin h → {θ : Fin (tRel X M lam) → X × Bool // RelBalanced (M lam) θ})

/-- The coins of `SampleSt_rel,i`: the honest reference state `Θ⁰`, the full observation `D` and
the permutations `π_{j,ζ}`. -/
abbrev RelBase (X : Type) [Fintype X] (Y : Fin k → Type) (M : ℕ → ℕ) (lam h : ℕ) : Type :=
  RelSec X M lam × (Fin (nRel X M lam) → ∀ j, Y j) × (Fin (M lam) → Fin h → Equiv.Perm (Fin (tRel X M lam)))

set_option synthInstance.maxSize 2048 in
open Classical in
/-- The law of the coins of `SampleSt_rel,i` (p.27: "Sample the honest reference experiment
`(Θ⁰, D)`"): `Θ⁰ ← Gen_rel,i(1^λ)` (uniform), `D ← Cⁿ(Word_rel,i(Θ⁰))`, and independent uniform
permutations `π_{j,ζ}` preserving the equal-`D_j` position sets. -/
noncomputable def relBaseW (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (M : ℕ → ℕ) (i : Fin k) (lam h : ℕ) (b : RelBase X Y M lam h) : ℝ :=
  unifW (RelSec X M lam) b.1 *
    (∏ p, jointP C ((releaseHalf C apx β M i).word lam b.1 p) (b.2.1 p)) *
    ∏ j, ∏ ζ, presW (rowOf b.2.1 j) (b.2.2 j ζ)

/-- The sampler state returned by `SampleSt_rel,i` on its coins (p.27): `H = Q_{Θ⁰}(D_i)`,
`J_j = J(θ⁰_j, D_j)`, `Φ_j = Φ_{i,θ⁰_j}(D_{i,j})`, `T_j(ζ) = π_{j,ζ} θ⁰_j`; "Discard `Θ⁰` and return
`st = (D, H, J, Φ, T)`". -/
noncomputable def relStOf (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (M : ℕ → ℕ) (i : Fin k) (lam h : ℕ) (b : RelBase X Y M lam h) :
    RelSt X Y M lam h :=
  (b.2.1, relQ C apx β i M lam b.1 (fun p => b.2.1 p i),
    fun j => signedWeight (b.1 j).1 (rowOf b.2.1 j),
    fun j => rowLabel C apx β i lam (b.1 j).1 (fun s => rowOf b.2.1 j s i),
    fun j ζ => ⟨permRow (b.2.2 j ζ) (b.1 j).1, relBalanced_permRow _ _ (b.1 j).2⟩)

open Classical in
/-- The **recovery algorithm of the release test** (Construction 5.11, `Rec_rel,i`, p.27): the empty
list if `H = 1`; otherwise, with `L^raw_j(w_j) = {ζ ∈ H_rel : h_{i,T_j(ζ)}(w_j) = 1}` if `Φ_j = R`
and `∅` if `Φ_j ≠ R`, and `L_j(w_j) = L^raw_j(w_j)` if `|L^raw_j(w_j)| ≤ ℓ_rel = M⁸`, `∅` otherwise,
return `Rec_{G_rel}(⋃_j {j} × L_j(w_j))`. -/
noncomputable def relRec (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (M : ℕ → ℕ) (i : Fin k) (lam : ℕ) (G : LayeredGraph (M lam))
    (st : RelSt X Y M lam G.h) (w : Fin (nRel X M lam) → Y i) : List (Fin G.κ → Bool) :=
  if st.2.1 then [] else
  let raw : Fin (M lam) → Finset (Fin G.h) := fun j =>
    if st.2.2.2.1 j = 1 then Finset.univ.filter fun ζ =>
      relCheck C apx i lam (st.2.2.2.2 j ζ).1 (rowOf w j) ∧
        0 ≤ relScore (β i) (st.2.2.2.2 j ζ).1 (rowOf w j)
    else ∅
  let L : Fin (M lam) → Finset (Fin G.h) := fun j => if (raw j).card ≤ M lam ^ 8 then raw j else ∅
  G.recov (Finset.univ.filter fun p : Fin (M lam) × Fin G.h => p.2 ∈ L p.1)

/-- The encoding of a release sampler state: the symbols of `D`, the bit `H`, the signed weights in
binary (in a fixed enumeration), the labels in two bits, and the candidate rows (symbol and sign
of each entry). -/
noncomputable def relStEnc {M : ℕ → ℕ} {lam h : ℕ} (st : RelSt X Y M lam h) : List Bool :=
  QAdvFew.PoQOracle.tup [wordEnc (∀ j, Y j) st.1, [st.2.1],
    (List.ofFn fun j : Fin (M lam) => (List.ofFn fun a : Fin (Fintype.card X) =>
      (List.ofFn fun e : Fin 2 => (List.ofFn fun c : Fin (Fintype.card (∀ j, Y j)) =>
        binW (Nat.size (tRel X M lam)) (st.2.2.1 j ((Fintype.equivFin X).symm a) (e = 1)
          ((Fintype.equivFin (∀ j, Y j)).symm c)).val).flatten).flatten).flatten).flatten,
    (List.ofFn fun j => binW 2 (st.2.2.2.1 j).val).flatten,
    (List.ofFn fun j : Fin (M lam) => (List.ofFn fun ζ : Fin h => (List.ofFn fun s =>
      symEnc X (symWidth X) ((st.2.2.2.2 j ζ).1 s).1 ++ [((st.2.2.2.2 j ζ).1 s).2]).flatten).flatten).flatten]

set_option synthInstance.maxSize 2048 in
open Classical in
/-- **Construction 5.11 (Release test)** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), pp.26–27), with the channel-consistency check, the preserved bits `β`, and the release
expander `G_rel` of the family `Gr`:
* `Gen_rel,i`, `Word_rel,i`, `Q_Θ`: the protocol half `releaseHalf`;
* `SampleSt_rel,i(1^λ)`: sample `(Θ⁰, D)`, record `H = Q_{Θ⁰}(D_i)`, the signed weights
  `J_j = J(θ⁰_j, D_j)`, the labels `Φ_j = Φ_{i,θ⁰_j}(D_{i,j})` (5.12), the candidate rows
  `T_j(ζ) = π_{j,ζ} θ⁰_j` for independent uniform permutations preserving the equal-`D_j` position
  sets, and return `st = (D, H, J, Φ, T)` with `obs(st) = D` and `H(st) = H`;
* `Recons_rel,i(st, σ)`: `θ_j = T_j(γ^rel_j(σ))`; `Rec_rel,i(st, w)`: `relRec`.

**Formalization Note** The law of `SampleSt` is the push-forward of the law of its coins (exact
reference distribution, p.24). Queries are typed words, so there are no malformed queries. -/
noncomputable def releaseTest (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (β : ∀ i, X → Y i → Bool) (M : ℕ → ℕ) (i : Fin k) (Gr : (M ℓ G : ℕ) → LayeredGraph M) :
    ChannelTest k X Y i (nRel X M) Finset.univ where
  toTestHalf := releaseHalf C apx β M i
  κ lam := (gRel Gr M lam).κ
  St lam := RelSt X Y M lam (gRel Gr M lam).h
  finSt lam := by classical exact inferInstance
  sampW lam st := wprob (relBaseW C apx β M i lam (gRel Gr M lam).h)
    (fun b => relStOf C apx β M i lam (gRel Gr M lam).h b = st)
  encSt lam st := relStEnc st
  obs lam st j p := st.1 p j
  H lam st := st.2.1
  recons lam st σ := fun j => st.2.2.2.2 j ((gRel Gr M lam).γ j σ)
  recov lam st w := relRec C apx β M i lam (gRel Gr M lam) st w

end NoisyOWMPC


