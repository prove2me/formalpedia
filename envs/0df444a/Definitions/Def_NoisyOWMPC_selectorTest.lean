-- Prove2me | Definitions.Def_NoisyOWMPC_selectorTest
-- name    : NoisyOWMPC_selectorTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:56:00.168118+00:00
-- url     : https://prove2.me/theorems/eb7c75b3-46b7-4fd9-8297-9374ee69eae3
-- title:
--   Construction 5.17: the subset selector with its proof-side algorithms
-- statement:
--   With the parameters of §5.2.3, the deletion budget $W=3r_N$, the agreement $G_{\mathrm{sel}}=\lceil m^{0.45}\rceil$, the hit threshold $\tau_{\mathrm{sel}}=\lceil\gamma_{\mathrm{sel}}G_{\mathrm{sel}}\sqrt{t_{\mathrm{sel}}}/m\rceil$, the list bound $\ell_{\mathrm{sel}}=\lceil100W/(\tau_{\mathrm{sel}}G_{\mathrm{sel}})\rceil$ and the expander $\mathcal G_{\mathrm{sel}}$, Construction 5.17 is:
--   1. $\mathrm{Gen}_{\mathrm{sel}}$, $\mathrm{Guard}_{\mathrm{sel}}$, $b_{\mathcal S}$ as in the protocol half;
--   2. $\mathrm{SampleSt}_{\mathrm{sel}}$: a table $\mathcal T=(S_{j,\zeta})$ of independent uniform $t_{\mathrm{sel}}$-subsets $S_{j,\zeta}\subseteq\mathcal N_j$;
--   3. $\mathrm{Recons}_{\mathrm{sel}}(\mathcal T,\xi)=(S_{j,\gamma_j(\xi)})_j$;
--   4. $\mathrm{Rec}_{\mathrm{sel}}(\mathcal T,V,U)$: with $\mathcal D=V\setminus U$, empty if $|\mathcal D|>W$; otherwise $L^{\mathrm{raw}}_j=\{\zeta:|\mathcal D\cap S_{j,\zeta}|\ge\tau_{\mathrm{sel}}\}$, truncated above $\ell_{\mathrm{sel}}$; return $\mathrm{Rec}_{\mathcal G_{\mathrm{sel}}}(\bigcup_j\{j\}\times L_j)$.
--
--   **Formalization Note** The expander is the graph of a family as in Corollary A.8; $\gamma_{\mathrm{sel}}$ is a rational parameter.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5.2.3, pp.28–29; Construction 5.17, pp.28–29

import Mathlib
import Definitions.Def_NoisyOWMPC_selectorHalf
import Definitions.Def_NoisyOWMPC_Selector
import Definitions.Def_NoisyOWMPC_LayeredGraph

namespace NoisyOWMPC

/-- The deletion budget `W = 3 r_N` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), §5.2.3 Parameters, p.28). -/
noncomputable def wSel (N : ℕ) : ℕ := 3 * rN N

/-- The agreement `G_sel = ⌈m^{0.45}⌉` (p.28). -/
noncomputable def gSel (N : ℕ) : ℕ := ⌈(mSel N : ℝ) ^ ((45 : ℝ) / 100)⌉₊

/-- The hit threshold `τ_sel = ⌈γ_sel G_sel √t_sel / m⌉` (p.28). -/
noncomputable def tauSel (γsel : ℚ) (N : ℕ) : ℕ :=
  ⌈(γsel : ℝ) * gSel N * Real.sqrt (tSel N) / mSel N⌉₊

/-- The list-size bound `ℓ_sel = ⌈100 W/(τ_sel G_sel)⌉` (p.28). -/
noncomputable def ellSel (γsel : ℚ) (N : ℕ) : ℕ :=
  ⌈(100 * wSel N : ℝ) / ((tauSel γsel N : ℝ) * gSel N)⌉₊

/-- The selector expander `G_sel`: the layered `(m ℓ_sel, G_sel, L_out)`-list-recoverable graph of
the family `Gr` with `m` layers (p.28). -/
noncomputable def gSelG (Gr : (M ℓ G : ℕ) → LayeredGraph M) (γsel : ℚ) (N : ℕ) :
    LayeredGraph (mSel N) :=
  Gr (mSel N) (ellSel γsel N) (gSel N)

open Classical in
/-- The **recovery algorithm of the selector** (Construction 5.17, `Rec_sel`, p.29): put
`D = V ∖ U` and return the empty list if `|D| > W`; otherwise, with
`L^raw_j(D) = {ζ ∈ H_sel : |D ∩ S_{j,ζ}| ≥ τ_sel}` and `L_j(D) = L^raw_j(D)` if
`|L^raw_j(D)| ≤ ℓ_sel`, `∅` otherwise, return `Rec_{G_sel}(⋃_j {j} × L_j(D))`. -/
noncomputable def selRec (γsel : ℚ) {N : ℕ} (G : LayeredGraph (mSel N))
    (T : Fin (mSel N) → Fin G.h → {S : Finset (Fin (Nbar N)) // S.card = tSel N})
    (V U : Finset (Fin N)) : List (Fin G.κ → Bool) :=
  let D := V \ U
  if wSel N < D.card then [] else
  let raw : Fin (mSel N) → Finset (Fin G.h) := fun j =>
    Finset.univ.filter fun ζ => tauSel γsel N ≤ segCount N D j (T j ζ).1
  let L : Fin (mSel N) → Finset (Fin G.h) := fun j =>
    if (raw j).card ≤ ellSel γsel N then raw j else ∅
  G.recov (Finset.univ.filter fun p : Fin (mSel N) × Fin G.h => p.2 ∈ L p.1)

open Classical in
/-- **Construction 5.17 (Subset selector)** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript
sha256 3a9569fa…), pp.28–29), with the parameters of §5.2.3, the hit-threshold constant `γ_sel`,
and the selector expander `G_sel` of the family `Gr`:
* `Gen_sel`, `Guard_sel`, `b_S`: the protocol half `selectorHalf`;
* `SampleSt_sel(1^λ)`: "For each `j ∈ [m]` and `ζ ∈ H_sel`, sample an independent uniform
  `t_sel`-subset `S_{j,ζ} ⊆ N_j`, and return the table `T = (S_{j,ζ})_{j,ζ}`" (uniform law on
  tables);
* `Recons_sel(T, ξ) = (S_{j,γ^sel_j(ξ)})_{j ∈ [m]}`; `Rec_sel(T, V, U)`: `selRec`.

**Formalization Note** Subsets of the segment `N_j` are subsets of `[N̄]` placed at the block
`j N̄, …, (j + 1) N̄ − 1` of `[N]` (`segCount`); a table entry is encoded by its indicator vector. -/
noncomputable def selectorTest (N : ℕ → ℕ) (Gr : (M ℓ G : ℕ) → LayeredGraph M) (γsel : ℚ) :
    Selector N where
  toSelHalf := selectorHalf N
  κ lam := (gSelG Gr γsel (N lam)).κ
  St lam := Fin (mSel (N lam)) → Fin (gSelG Gr γsel (N lam)).h →
    {S : Finset (Fin (Nbar (N lam))) // S.card = tSel (N lam)}
  finSt lam := inferInstance
  sampW lam := unifW _
  encSt lam T := (List.ofFn fun j => (List.ofFn fun ζ =>
    List.ofFn fun s => decide (s ∈ (T j ζ).1)).flatten).flatten
  recons lam T ξ := fun j => T j ((gSelG Gr γsel (N lam)).γ j ξ)
  recov lam T V U := selRec γsel (gSelG Gr γsel (N lam)) T V U

end NoisyOWMPC


