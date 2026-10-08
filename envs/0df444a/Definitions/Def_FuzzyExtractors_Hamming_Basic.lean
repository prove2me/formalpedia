-- Prove2me | Definitions.Def_FuzzyExtractors_Hamming_Basic
-- name    : FuzzyExtractors_Hamming_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:26.474851+00:00
-- url     : https://prove2.me/theorems/917be445-e6e9-454d-8454-1ea4d63e4f1a
-- title:
--   Min-entropy, average min-entropy, statistical distance, extractors, universal hashing, secure sketches, fuzzy extractors, and Constructions 1–3 (§2–§5, pp. 7–16)
-- statement:
--   This module fixes the objects of Dodis, Ostrovsky, Reyzin and Smith used for the Hamming-metric fuzzy extractor. All logarithms are base $2$. A random variable is identified with its law (a probability mass function); a pair of correlated random variables $(A,B)$ is a joint law on $\alpha\times\beta$, and a randomized procedure is a Markov kernel.
--
--   **Entropy and distance (§2.3–§2.4, pp. 8–9).**
--
--   1. The *min-entropy* of $A$ is $\mathbf H_\infty(A) = -\log \max_a \Pr[A=a]$.
--   2. The *average min-entropy* of $A$ given $B$ is
--   $$\tilde{\mathbf H}_\infty(A\mid B) = -\log\Big(\mathbb E_{b\leftarrow B}\big[\max_a \Pr[A=a\mid B=b]\big]\Big) = -\log \sum_b \max_a \Pr[A=a \wedge B=b].$$
--   3. The *statistical distance* is $\mathbf{SD}(A,B)=\tfrac12\sum_v |\Pr(A=v)-\Pr(B=v)|$, and $U_\ell$ is the uniform law on $\{0,1\}^\ell$.
--
--   **Extractors and universal hashing (§2.3–§2.5, pp. 8–10).** A function $\mathsf{Ext}(w;x)\in\{0,1\}^\ell$ with seed $x$ uniform on a finite nonempty set $X$ is a *strong extractor* with parameters $(m,\ell,\varepsilon)$ (Definition 1) if $\mathbf{SD}((\mathsf{Ext}(W;X),X),(U_\ell,X))\le\varepsilon$ for every $W$ with $\mathbf H_\infty(W)\ge m$; it is an *average-case* strong extractor (Definition 2) if $\mathbf{SD}((\mathsf{Ext}(W;X),X,I),(U_\ell,X,I))\le\varepsilon$ for every pair $(W,I)$ with $\tilde{\mathbf H}_\infty(W\mid I)\ge m$. Here $X$ is independent of $(W,I)$ and $U_\ell$ is independent of everything else. A family $\{H_x\}_{x\in X}$ of functions into $\{0,1\}^\ell$ is *universal* if $\Pr_{x\in X}[H_x(a)=H_x(b)] = 2^{-\ell}$ for all $a\ne b$.
--
--   **Codes (§2.2, pp. 7–8).** A finite set $C\subseteq\mathcal M$ is an $(\mathcal M,K,t)$-code, $K=|C|$, if every $w$ has at most one codeword $c$ with $\mathrm{dis}(w,c)\le t$. For $\mathcal M=\mathcal F^n$ with the Hamming distance, $C$ has minimum distance at least $d$ if distinct codewords differ in at least $d$ positions.
--
--   **Secure sketches (Definitions 3, 4, p. 11).** A pair of randomized procedures $(\mathsf{SS},\mathsf{Rec})$ is *correct* for $t$ if $\mathsf{Rec}(w',s)=w$ with certainty whenever $\mathrm{dis}(w,w')\le t$ and $s$ is a possible output of $\mathsf{SS}(w)$. It is an $(\mathcal M,m,\tilde m,t)$-*secure sketch* if moreover $\tilde{\mathbf H}_\infty(W\mid \mathsf{SS}(W))\ge\tilde m$ for every $W$ with $\mathbf H_\infty(W)\ge m$, and an *average-case* one if $\tilde{\mathbf H}_\infty(W\mid(\mathsf{SS}(W),I))\ge\tilde m$ for every pair $(W,I)$ with $\tilde{\mathbf H}_\infty(W\mid I)\ge m$.
--
--   **Fuzzy extractors (Definition 5, p. 12, and p. 13).** A pair $(\mathsf{Gen},\mathsf{Rep})$, where $\mathsf{Gen}(w)$ outputs $(R,P)$ with $R\in\{0,1\}^\ell$, is *correct* for $t$ if $\mathsf{Rep}(w',P)=R$ with certainty whenever $\mathrm{dis}(w,w')\le t$ and $(R,P)$ is a possible output of $\mathsf{Gen}(w)$. It is an $(\mathcal M,m,\ell,t,\varepsilon)$-*fuzzy extractor* if moreover $\mathbf{SD}((R,P),(U_\ell,P))\le\varepsilon$ whenever $\mathbf H_\infty(W)\ge m$, and an *average-case* one if $\mathbf{SD}((R,P,I),(U_\ell,P,I))\le\varepsilon$ whenever $\tilde{\mathbf H}_\infty(W\mid I)\ge m$.
--
--   **Constructions.**
--
--   1. *Construction 1* (p. 14), for a transitive family $\Pi$ of isometries of $\mathcal M$: $\mathsf{SS}(w)$ picks $b\in C$ uniformly, then $\pi\in\Pi$ uniformly among those with $\pi(w)=b$, and outputs $\pi$; $\mathsf{Rec}(w',\pi)$ decodes $\pi(w')$ to a codeword $b'$ and outputs $\pi^{-1}(b')$.
--   2. *Construction 2* (code-offset, p. 16): $\mathsf{SS}(w)=w-c$ for $c\in C$ uniform; $\mathsf{Rec}(w',s)$ decodes $w'-s$ to $c$ and outputs $c+s$.
--   3. *Construction 3* (syndrome, p. 16), for a linear code with syndrome map $\mathrm{syn}$: $\mathsf{SS}(w)=\mathrm{syn}(w)$; $\mathsf{Rec}(w',s)$ finds $e$ of Hamming weight $\le t$ with $\mathrm{syn}(e)=\mathrm{syn}(w')-s$ and outputs $w'-e$.
--   4. *The construction of Lemma 4.1* (p. 13): $\mathsf{Gen}(w)$ outputs $R=\mathsf{Ext}(w;x)$ and $P=(\mathsf{SS}(w),x)$ for a fresh uniform seed $x$; $\mathsf{Rep}(w',(s,x))$ outputs $\mathsf{Ext}(\mathsf{Rec}(w',s);x)$.
--
--   These definitions form the common vocabulary for the paper's four missions.
--
--   **Formalization Note** Laws are `PMF`s. Average min-entropy is written in the joint form $-\log\sum_b\max_a\Pr[A=a\wedge B=b]$, which equals the paper's expectation because $\Pr[B=b]\max_a\Pr[A=a\mid B=b]=\max_a\Pr[A=a\wedge B=b]$, and needs no conditioning on null events. The auxiliary variable $I$ ranges over every type, which contains the paper's $\{0,1\}^*$. Sketch and helper strings take values in arbitrary types rather than bit strings; $\{0,1\}^\ell$ is `Fin ℓ → Bool`. Extractor inputs and seeds range over an arbitrary type and an arbitrary finite nonempty set rather than $\{0,1\}^n$ and $\{0,1\}^r$. The "efficient" (polynomial-time) clauses of Definitions 1–5 are dropped: there is no complexity substrate. "Decoding" returns a codeword within distance $t$ when one exists; for an $(\mathcal M,K,t)$-code this is the unique, hence the closest, such codeword, which is all correctness uses. The Hamming space $\mathcal F^n$ is `Fin n → F` for any finite additive commutative group $F$ (the paper's additive cyclic group is a special case); the syndrome map is any linear map $\mathcal F^n\to\mathcal F^{n-k}$ whose kernel is the code. Metric axioms are not built in; a theorem that needs one states it.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, §2.1–§3.2 and §4.1–§5, Definitions 1–5, Constructions 1–3, pp. 7–16

import Mathlib

namespace FuzzyExtractors.Hamming

open scoped ENNReal

noncomputable section

/-! ### Shared model (§2.3–§3.2, pp. 8–13) -/

/-- Min-entropy H∞(A) = −log max_a Pr[A = a] (§2.3, p. 8). -/
def minEntropy {α : Type*} (A : PMF α) : ℝ :=
  -Real.logb 2 (⨆ a, A a).toReal

/-- Average min-entropy H̃∞(A | B) = −log E_{b←B}[max_a Pr[A = a | B = b]] (§2.4, p. 9),
written in the equivalent joint form −log Σ_b max_a Pr[A = a ∧ B = b]. -/
def avgMinEntropy {α β : Type*} (AB : PMF (α × β)) : ℝ :=
  -Real.logb 2 (∑' b, ⨆ a, AB (a, b)).toReal

/-- Statistical distance SD(A, B) = ½ Σ_v |Pr(A = v) − Pr(B = v)| (§2.3, p. 8). -/
def statDist {α : Type*} (A B : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑' v, |(A v).toReal - (B v).toReal|

/-- U_ℓ, the uniform distribution on ℓ-bit strings (§2, p. 7). -/
def uniformBits (ℓ : ℕ) : PMF (Fin ℓ → Bool) := PMF.uniformOfFintype _

/-- Correctness of a secure sketch (Definition 3, item 2). -/
def SketchCorrect {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  ∀ w w', dis w w' ≤ t → ∀ s ∈ (SS w).support, Rec w' s = PMF.pure w

/-- The joint law of (W, SS(W)). -/
def withSketch {M S : Type} (SS : M → PMF S) (W : PMF M) : PMF (M × S) :=
  W.bind fun w => (SS w).map fun s => (w, s)

/-- The joint law of (W, (SS(W), I)) from the joint law of (W, I). -/
def withSketchAux {M S ι : Type} (SS : M → PMF S) (WI : PMF (M × ι)) : PMF (M × (S × ι)) :=
  WI.bind fun p => (SS p.1).map fun s => (p.1, (s, p.2))

/-- An (M, m, m̃, t)-secure sketch (Definition 3). -/
def IsSecureSketch {M S : Type} (dis : M → M → ℕ) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  SketchCorrect dis t SS Rec ∧
    ∀ W : PMF M, m ≤ minEntropy W → m' ≤ avgMinEntropy (withSketch SS W)

/-- An average-case (M, m, m̃, t)-secure sketch (Definition 4). -/
def IsAvgSecureSketch {M S : Type} (dis : M → M → ℕ) (m m' : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) : Prop :=
  SketchCorrect dis t SS Rec ∧
    ∀ (ι : Type) (WI : PMF (M × ι)), m ≤ avgMinEntropy WI →
      m' ≤ avgMinEntropy (withSketchAux SS WI)

/-- Correctness of a fuzzy extractor (Definition 5, item 2). -/
def ExtractorCorrect {M P : Type} {ℓ : ℕ} (dis : M → M → ℕ) (t : ℕ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ∀ w w', dis w w' ≤ t → ∀ rp ∈ (Gen w).support, Rep w' rp.2 = PMF.pure rp.1

/-- An (M, m, ℓ, t, ε)-fuzzy extractor (Definition 5): SD((R, P), (U_ℓ, P)) ≤ ε. -/
def IsFuzzyExtractor {M P : Type} (dis : M → M → ℕ) (m : ℝ) (ℓ t : ℕ) (ε : ℝ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ExtractorCorrect dis t Gen Rep ∧
    ∀ W : PMF M, m ≤ minEntropy W →
      statDist (W.bind Gen)
        ((W.bind Gen).bind fun rp => (uniformBits ℓ).map fun u => (u, rp.2)) ≤ ε

/-- The average-case variant (p. 13): if H̃∞(W | I) ≥ m then SD((R, P, I), (U_ℓ, P, I)) ≤ ε. -/
def IsAvgFuzzyExtractor {M P : Type} (dis : M → M → ℕ) (m : ℝ) (ℓ t : ℕ) (ε : ℝ)
    (Gen : M → PMF ((Fin ℓ → Bool) × P)) (Rep : M → P → PMF (Fin ℓ → Bool)) : Prop :=
  ExtractorCorrect dis t Gen Rep ∧
    ∀ (ι : Type) (WI : PMF (M × ι)), m ≤ avgMinEntropy WI →
      statDist (WI.bind fun p => (Gen p.1).map fun rp => (rp.1, rp.2, p.2))
        ((WI.bind fun p => (Gen p.1).map fun rp => (rp.1, rp.2, p.2)).bind
          fun x => (uniformBits ℓ).map fun u => (u, x.2.1, x.2.2)) ≤ ε

/-! ### Strong extractors and universal hashing (§2.3–§2.5, pp. 8–10) -/

/-- A family `{H_x : α → {0,1}^ℓ}_{x ∈ X}` is universal (Lemma 2.1, p. 9):
for all `a ≠ b`, `Pr_{x ∈ X}[H_x(a) = H_x(b)] = 2^{−ℓ}`, `x` uniform on `X`. -/
def IsUniversal {α X : Type} [Fintype X] {ℓ : ℕ} (H : X → α → (Fin ℓ → Bool)) : Prop :=
  ∀ a b, a ≠ b →
    ((Finset.univ.filter fun x => H x a = H x b).card : ℝ) / Fintype.card X = (2 : ℝ) ^ (-(ℓ : ℤ))

/-- The joint law of (Ext(W; X), X), with the seed X uniform on `X` and independent of W. -/
def extractLaw {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (Ext : α → X → (Fin ℓ → Bool)) (W : PMF α) : PMF ((Fin ℓ → Bool) × X) :=
  W.bind fun w => (PMF.uniformOfFintype X).map fun x => (Ext w x, x)

/-- The joint law of (Ext(W; X), X, I) from the joint law of (W, I), with X uniform and
independent of (W, I). -/
def extractLawAux {α X ι : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (Ext : α → X → (Fin ℓ → Bool)) (WI : PMF (α × ι)) : PMF ((Fin ℓ → Bool) × X × ι) :=
  WI.bind fun p => (PMF.uniformOfFintype X).map fun x => (Ext p.1 x, x, p.2)

/-- An (n, m, ℓ, ε)-strong extractor (Definition 1, p. 8), for a finite input set `α` and a
finite nonempty seed set `X`: for every W with H∞(W) ≥ m, SD((Ext(W; X), X), (U_ℓ, X)) ≤ ε. -/
def IsStrongExtractor {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ} (m ε : ℝ)
    (Ext : α → X → (Fin ℓ → Bool)) : Prop :=
  ∀ W : PMF α, m ≤ minEntropy W →
    statDist (extractLaw Ext W)
      ((extractLaw Ext W).bind fun y => (uniformBits ℓ).map fun u => (u, y.2)) ≤ ε

/-- An average-case (n, m, ℓ, ε)-strong extractor (Definition 2, p. 10): for every pair (W, I)
with H̃∞(W | I) ≥ m, SD((Ext(W; X), X, I), (U_ℓ, X, I)) ≤ ε. -/
def IsAvgStrongExtractor {α X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ} (m ε : ℝ)
    (Ext : α → X → (Fin ℓ → Bool)) : Prop :=
  ∀ (ι : Type) (WI : PMF (α × ι)), m ≤ avgMinEntropy WI →
    statDist (extractLawAux Ext WI)
      ((extractLawAux Ext WI).bind fun y => (uniformBits ℓ).map fun u => (u, y.2.1, y.2.2)) ≤ ε

/-! ### Codes (§2.2, pp. 7–8) -/

/-- An (M, K, t)-code with K = |C| (§2.2, p. 8): every w ∈ M has at most one codeword c with
dis(w, c) ≤ t. -/
def IsCode {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ) : Prop :=
  ∀ w, ∀ c ∈ C, ∀ c' ∈ C, dis w c ≤ t → dis w c' ≤ t → c = c'

/-- The code C ⊆ 𝓕^n has minimum Hamming distance at least d (§2.2, p. 7). -/
def MinDistGe {F : Type} [DecidableEq F] {n : ℕ} (C : Finset (Fin n → F)) (d : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c'

/-- A codeword within distance t of y, if one exists (otherwise y itself, with no guarantee).
For an (M, K, t)-code it is the unique such codeword, hence the closest codeword. -/
def decodeWithin {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ) (y : M) : M :=
  open Classical in
  if h : ∃ c ∈ C, dis y c ≤ t then h.choose else y

/-! ### Construction 1: the sketch for transitive metric spaces (§4.2, p. 14) -/

/-- Construction 1, SS: pick b ∈ C uniformly, then π ∈ Π uniformly among those with
π(w) = b, and output π. Transitivity makes the second set nonempty. -/
def transSS {M Pm : Type} [Fintype Pm] [DecidableEq M] (C : Finset M) (hC : C.Nonempty)
    (act : Pm → M ≃ M) (htrans : ∀ a b, ∃ π, act π a = b) (w : M) : PMF Pm :=
  (PMF.uniformOfFinset C hC).bind fun b =>
    PMF.uniformOfFinset (Finset.univ.filter fun π => act π w = b)
      (by
        obtain ⟨π, hπ⟩ := htrans w b
        exact ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ π, hπ⟩⟩)

/-- Construction 1, Rec: decode π(w′) to a codeword b′ and output π⁻¹(b′). -/
def transRec {M Pm : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ)
    (act : Pm → M ≃ M) (w' : M) (π : Pm) : PMF M :=
  PMF.pure ((act π).symm (decodeWithin dis C t (act π w')))

/-! ### Constructions 2 and 3: code-offset and syndrome sketches (§5, p. 16) -/

/-- Construction 2, SS: pick c ∈ C uniformly and output w − c. -/
def codeOffsetSS {F : Type} [AddCommGroup F] {n : ℕ} (C : Finset (Fin n → F))
    (hC : C.Nonempty) (w : Fin n → F) : PMF (Fin n → F) :=
  (PMF.uniformOfFinset C hC).map fun c => w - c

/-- Construction 2, Rec: decode c′ = w′ − s to c and output c + s. -/
def codeOffsetRec {F : Type} [AddCommGroup F] [DecidableEq F] {n : ℕ}
    (C : Finset (Fin n → F)) (t : ℕ) (w' s : Fin n → F) : PMF (Fin n → F) :=
  PMF.pure (decodeWithin hammingDist C t (w' - s) + s)

/-- Construction 3, SS: output the syndrome syn(w) (deterministic). -/
def syndromeSS {F : Type} [Field F] {n r : ℕ} (syn : (Fin n → F) →ₗ[F] (Fin r → F))
    (w : Fin n → F) : PMF (Fin r → F) :=
  PMF.pure (syn w)

/-- Construction 3, Rec: find e of Hamming weight ≤ t with syn(e) = syn(w′) − s (if one
exists; otherwise e = 0, with no guarantee) and output w′ − e. -/
def syndromeRec {F : Type} [Field F] [DecidableEq F] {n r : ℕ}
    (syn : (Fin n → F) →ₗ[F] (Fin r → F)) (t : ℕ) (w' : Fin n → F) (s : Fin r → F) :
    PMF (Fin n → F) :=
  open Classical in
  PMF.pure (w' - if h : ∃ e : Fin n → F, hammingNorm e ≤ t ∧ syn e = syn w' - s
    then h.choose else 0)

/-! ### The construction of Lemma 4.1 (§4.1, p. 13) -/

/-- Lemma 4.1, Gen(w; r, x): P = (SS(w; r), x), R = Ext(w; x), output (R, P);
x uniform on the seed set X, independent of the sketch's coins. -/
def sketchExtGen {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (w : M) : PMF ((Fin ℓ → Bool) × (S × X)) :=
  (SS w).bind fun s => (PMF.uniformOfFintype X).map fun x => (Ext w x, (s, x))

/-- Lemma 4.1, Rep(w′, (s, x)): recover w = Rec(w′, s) and output Ext(w; x). -/
def sketchExtRep {M S X : Type} {ℓ : ℕ}
    (Rec : M → S → PMF M) (Ext : M → X → (Fin ℓ → Bool)) (w' : M) (p : S × X) :
    PMF (Fin ℓ → Bool) :=
  (Rec w' p.1).map fun w => Ext w p.2

end

end FuzzyExtractors.Hamming


