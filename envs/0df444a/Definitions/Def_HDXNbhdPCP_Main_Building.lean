-- Prove2me | Definitions.Def_HDXNbhdPCP_Main_Building
-- name    : HDXNbhdPCP_Main_Building
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:45.997606+00:00
-- url     : https://prove2.me/theorems/996d0521-9124-47c8-8a66-ed82520f3e69
-- title:
--   Spherical buildings $\mathcal X(\mathbb F_q^n)$, opposite complexes $O_\sigma$, $\theta_{I,\emptyset}$ and the Kac–Moody–Steinberg complex $A_{q,d,s}$ (Definitions 6.2, 6.3, 6.7)
-- statement:
--   Let $K=\mathbb F_q$ be a finite field and $V=K^n$.
--
--   1. **Spherical building (Definition 6.2).** $\mathcal X(V)$ is the $(n-1)$-partite flag complex whose colour-$i$ vertices are the $i$-dimensional subspaces of $V$ ($1\le i\le n-1$); its facets are the maximal flags $W_1<\dots<W_{n-1}$, $\dim W_i=i$, with the uniform distribution.
--   2. **Opposite complex (Definition 6.3).** For a maximal flag $\sigma=(E_1<\dots<E_{n-1})$, $O_\sigma(V)$ is the induced subcomplex with parts $O[i]=\{W:\dim W=i,\ W\cap E_{n-i}=0\}$; its facets are the maximal flags all of whose members lie in these parts, with the uniform distribution.
--   3. **Density (p. 39).** For $\emptyset\ne I\subseteq[n-1]$,
--   $$\theta_{I,\emptyset}=\Pr_{R\sim\mathcal X[I]}\big[R\in O[I]\big].$$
--   4. **KMS complex (Definition 6.7).** For $\mu\in\mathbb F_q[t]$ (irreducible of degree $s$ in the paper) let $G=\mathrm{SL}_{d+1}(\mathbb F_q[t]/(\mu))$ with coordinates $0,\dots,d$, $x_{i,j}(r)$ the elementary matrix with $r$ at $(i,j)$, $U_i=\{x_{i,i+1}(a):a\in\mathbb F_q\}$ for $i<d$, $U_d=\{x_{d,0}(bt):b\in\mathbb F_q\}$, and $H_i=\langle U_j:j\ne i\rangle$. Then $A_{q,d,s}$ is the coset complex of $G$ with respect to $H_0,\dots,H_d$, coloured by $\mathbb Z_{d+1}$: the facet of $g\in G$ is $(gH_0,\dots,gH_d)$.
--   5. The vertex link $A_v$ of a colour-$i$ vertex, with colours renamed by $i+j\mapsto j$ ($j\in[d]$), is a complex on the colours of $\mathcal X(\mathbb F_q^{d+1})$.
--
--   These complexes are the building blocks of the paper's sparse sound agreement tests (Lemmas 6.9–6.11, Theorem 6.1).
--
--   **Formalization Note** $V$ is `Fin n → K`, colours are the dimensions $1,\dots,n-1$ (`Finset.Ioo 0 n`), and a vertex is a `Submodule`. The opposite complex is defined for an arbitrary maximal flag; Definition 6.3 uses the standard flag of an ordered basis, and every maximal flag is of that form. $\mathbb F_q[t]/(\mu)$ is `AdjoinRoot μ`, and $G$ is `Matrix.SpecialLinearGroup`. The paper does not name the facet distribution of the coset complex; it is taken to be the image of the uniform distribution on $G$, which is uniform on facets because the fibres are cosets of one subgroup. Colours $\mathbb Z_{d+1}$ are `Fin (d+1)` with modular addition.
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), pp. 39-40, Definitions 6.2, 6.3, 6.7 and the definition of θ_{I,J} (p. 39)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

/-!
# Spherical buildings, opposite complexes and Kac–Moody–Steinberg complexes
(Dikstein–Dinur–Hopkins–Singer, §6.1–6.2, Definitions 6.2, 6.3, 6.7)

The `n`-dimensional space over the finite field `K` is `Fin n → K`; the colours of the building
are the dimensions `1, …, n − 1` (`BColor n`), and a vertex of colour `i` is an `i`-dimensional
subspace.
-/

namespace HDXNbhdPCP.Main

open Classical Polynomial

noncomputable section

/-- The colours `{1, …, n − 1}` of the spherical building of an `n`-dimensional space. -/
abbrev BColor (n : ℕ) := ↥(Finset.Ioo 0 n)

/-- The complementary colour `n − i`. -/
def BColor.comp {n : ℕ} (i : BColor n) : BColor n :=
  ⟨n - i.1, by
    have h := Finset.mem_Ioo.mp i.2
    exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩⟩

variable (K : Type) [Field K] [Fintype K]

/-- A maximal flag `W₁ < W₂ < ⋯ < W_{n−1}` of `Fin n → K`, `dim W_i = i`. -/
def IsMaxFlag {n : ℕ} (F : BColor n → Submodule K (Fin n → K)) : Prop :=
  (∀ i, Module.finrank K (F i) = i.1) ∧ ∀ i j : BColor n, i.1 ≤ j.1 → F i ≤ F j

/-- The finite set of maximal flags. -/
def maxFlags (n : ℕ) : Finset (BColor n → Submodule K (Fin n → K)) :=
  Finset.univ.filter (IsMaxFlag K)

/-- Definition 6.2: the spherical building `𝒳(V)` of `V = 𝔽_q^n`, the `(n−1)`-partite flag complex
of nontrivial subspaces (colour `i` = `i`-dimensional subspaces), with the uniform distribution on
maximal flags. -/
def building (n : ℕ) : ColoredComplex (BColor n) (fun _ => Submodule K (Fin n → K)) :=
  FinDist.uniform (maxFlags K n)

/-- Definition 6.3: the opposite complex `O_σ(V)` relative to the maximal flag
`σ = (E₁ < ⋯ < E_{n−1})`: the induced subcomplex of `𝒳(V)` with parts
`O[i] = {W : dim W = i, W ∩ E_{n−i} = 0}`, with the uniform distribution on its maximal flags. -/
def opposite (n : ℕ) (E : BColor n → Submodule K (Fin n → K)) :
    ColoredComplex (BColor n) (fun _ => Submodule K (Fin n → K)) :=
  FinDist.uniform ((maxFlags K n).filter (fun F => ∀ i, F i ⊓ E i.comp = ⊥))

/-- `θ_{I,∅} = P_{R ∼ 𝒳[I]}[R ∈ O[I]]` (p. 39): the probability that the `I`-face of a uniform
maximal flag of `𝒳(V)` is a face of the opposite complex. -/
def thetaEmpty (n : ℕ) (E : BColor n → Submodule K (Fin n → K)) (I : Finset (BColor n)) : ℝ :=
  ((building K n).faceDist I).prob (fun R => R ∈ ((opposite K n E).faceDist I).supp)

/-- The colours of the building whose dimension lies in the set `S` (used for regroupings such as
`𝒳[1 ↦ {a, e}, 2 ↦ {c}, 3 ↦ {b, d}]`). -/
def bcolorsOf (n : ℕ) (S : Finset ℕ) : Finset (BColor n) := Finset.univ.filter (fun i => i.1 ∈ S)

/-- The colours `i ∈ ℤ_{d+1}` (`Fin (d+1)`) whose value lies in the set `S`. -/
def fcolorsOf (d : ℕ) (S : Finset ℕ) : Finset (Fin (d + 1)) := Finset.univ.filter (fun i => i.1 ∈ S)

/-- The coefficient ring `𝔽_q[t]/(μ)`. -/
abbrev KMSRing (mu : K[X]) := AdjoinRoot mu

/-- The group `G = SL_{d+1}(𝔽_q[t]/(μ))`, coordinates indexed by `{0, …, d}` (`Fin (d+1)`). -/
abbrev KMSGroup (d : ℕ) (mu : K[X]) := Matrix.SpecialLinearGroup (Fin (d + 1)) (KMSRing K mu)

/-- The entry of the root subgroup `U_i`: `a` for `i < d`, `a·t` for `i = d`. -/
def kmsEntry (d : ℕ) (mu : K[X]) (i : Fin (d + 1)) (a : K) : KMSRing K mu :=
  if i = Fin.last d then AdjoinRoot.of mu a * AdjoinRoot.root mu else AdjoinRoot.of mu a

/-- `U_i = {x_{i,i+1}(a) : a ∈ 𝔽_q}` for `i < d` and `U_d = {x_{d,0}(b t) : b ∈ 𝔽_q}` (indices
mod `d + 1`), where `x_{i,j}(r)` is the elementary matrix with `r` at `(i, j)`. -/
def kmsU (d : ℕ) (mu : K[X]) (i : Fin (d + 1)) : Set (KMSGroup K d mu) :=
  {g | ∃ a : K, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) (KMSRing K mu)) =
    Matrix.transvection i (i + 1) (kmsEntry K d mu i a)}

/-- `H_i = ⟨U_j : j ≠ i⟩`. -/
def kmsH (d : ℕ) (mu : K[X]) (i : Fin (d + 1)) : Subgroup (KMSGroup K d mu) :=
  Subgroup.closure (⋃ j ∈ ({i}ᶜ : Set (Fin (d + 1))), kmsU K d mu j)

/-- Definition 6.7: the KMS complex `A_{q,d,s}` for `μ ∈ 𝔽_q[t]` (irreducible of degree `s` in
the paper): the coset complex of `G` with respect to `H_0, …, H_d`, coloured by `ℤ_{d+1}`
(`Fin (d+1)`); the facet of `g ∈ G` is `(g H_0, …, g H_d)`, and the facet distribution is the
image of the uniform distribution on `G`. -/
def kms (d : ℕ) (mu : K[X]) (hmu : mu ≠ 0) :
    ColoredComplex (Fin (d + 1)) (fun i => KMSGroup K d mu ⧸ kmsH K d mu i) :=
  letI : Finite (KMSRing K mu) :=
    @Module.finite_of_finite K _ _ _ _ _ (AdjoinRoot.powerBasis hmu).finite
  letI : Fintype (KMSGroup K d mu) := Fintype.ofFinite _
  FinDist.map (FinDist.uniform (Finset.univ : Finset (KMSGroup K d mu)))
    (fun g i => (QuotientGroup.mk g : KMSGroup K d mu ⧸ kmsH K d mu i))

/-- A colour `j ∈ {1, …, d}` of the building of `𝔽_q^{d+1}` viewed as an element of `ℤ_{d+1}`. -/
def bcolorToFin {d : ℕ} (j : BColor (d + 1)) : Fin (d + 1) :=
  ⟨j.1, (Finset.mem_Ioo.mp j.2).2⟩

/-- The vertex link `A_v` of the facet coordinate `v = y_i` in `A = A_{q,d,s}`, with its colours
renamed by `i + j ↦ j` for `j ∈ [d]`; the colours `1, …, d` are those of the building of
`𝔽_q^{d+1}`. -/
def kmsLink (d : ℕ) (mu : K[X]) (hmu : mu ≠ 0) (i : Fin (d + 1))
    (y : (j : Fin (d + 1)) → KMSGroup K d mu ⧸ kmsH K d mu j) :
    ColoredComplex (BColor (d + 1))
      (fun j => KMSGroup K d mu ⧸ kmsH K d mu (i + bcolorToFin j)) :=
  FinDist.map ((kms K d mu hmu).condFace {i} y) (fun x j => x (i + bcolorToFin j))

end

end HDXNbhdPCP.Main


