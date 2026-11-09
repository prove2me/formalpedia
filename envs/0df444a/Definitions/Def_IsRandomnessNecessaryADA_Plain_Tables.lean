-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables
-- name    : IsRandomnessNecessaryADA_Plain_Tables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:15.790834+00:00
-- url     : https://prove2.me/theorems/39badf4c-f63a-4686-9a85-cdc31a50e59c
-- title:
--   Hidden supports, full-table completions and replayed response profiles
-- statement:
--   Let $X=[N]\times[M]$ and let $r\in[M]^N$ specify the $N$ distinct support points $(i,r_i)$. Their uniform law is $P_r$; an ordered row sample $s\in[N]^n$ becomes $S_r(s)=((s_t,r_{s_t}))_t$. The law $\mu$ is uniform on all Boolean $N\times M$ tables. Overwriting only the support cells of a $\mu$-table with pattern $v$ gives $\mu_{r,v}$, leaving every other cell an independent fair bit.
--
--   For a fixed list $h$ of past tables, replay is performed separately on every candidate sample. The response profile is
--   $$V_i^h(q)=\bigl(\mathbf1\{m(S_r(s),\operatorname{replay}(S_r(s),h),q)\ge1/2\}\bigr)_{s\in([N]\setminus\{i\})^n}.$$
--   It includes every sample omitting row $i$, not only surviving ones. The simultaneous profile-agreement predicate states equality across every actual changed row of a threshold path. The density factor is $D=(N+1)2^N$. The column-count definition records the integer-valued witness from Eq.(10), using $N=20n$ and the exact horizon. These are computed objects, not hypotheses about a successful attack.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), §§4.2–4.3, pp.10–11, Eq.(2); §4.4, pp.12–14, Eqs.(5),(10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

abbrev Table (N M : ℕ) := BooleanQuery (Fin N × Fin M)
abbrev Locations (N M : ℕ) := Fin N → Fin M

/-- Section 4.2: support points have distinct first coordinates. -/
def supportEmbedding {N M : ℕ} (r : Locations N M) : Fin N ↪ (Fin N × Fin M) where
  toFun i := (i, r i)
  inj' := by intro i j h; exact congrArg Prod.fst h

noncomputable def hiddenLaw {N M : ℕ} (hN : 0 < N) (r : Locations N M) :
    PMF (Fin N × Fin M) := uniformSupport hN (supportEmbedding r)

def rowSample {N M n : ℕ} (r : Locations N M) (s : Fin n → Fin N) :
    Fin n → (Fin N × Fin M) := fun t => (s t, r (s t))

/-- Uniform tables give independent fair bits in every cell. -/
noncomputable def tableLaw (N M : ℕ) : PMF (Table N M) := PMF.uniformOfFintype _

/-- Overwrite only support cells; every other cell remains an independent fair bit.
This is the positive-mass conditional law μ_{r,v} in Section 4.2. -/
noncomputable def completeTable {N M : ℕ} (r : Locations N M)
    (v : BooleanQuery (Fin N)) (q : Table N M) : Table N M :=
  fun x => if x.2 = r x.1 then v x.1 else q x

noncomputable def completionLaw {N M : ℕ} (r : Locations N M)
    (v : BooleanQuery (Fin N)) : PMF (Table N M) :=
  (tableLaw N M).map (completeTable r v)

/-- Equation (2): all ordered samples avoiding i, not just surviving ones.
Each candidate replays its own real responses to the fixed past tables. -/
noncomputable def responseProfile {N M n : ℕ} (m : Mechanism (Fin N × Fin M) n)
    (r : Locations N M) (h : List (Table N M)) (i : Fin N) (q : Table N M) :
    (Fin n → {j : Fin N // j ≠ i}) → Bool :=
  fun s =>
    let S := rowSample r (fun t => (s t).val)
    responseBit (m S (replayQueries m S (h.map liftQuery)) (liftQuery q))

/-- The simultaneous equality event for the actual, possibly shorter, threshold path. -/
noncomputable def profilesAgree {N M n : ℕ} (m : Mechanism (Fin N × Fin M) n)
    (r : Locations N M) (h : List (Table N M)) (p : ThresholdPath N)
    (Q : Fin (p.length + 1) → Table N M) : Prop :=
  ∀ t : Fin p.length,
    responseProfile m r h (p.change t) (Q t.castSucc) =
      responseProfile m r h (p.change t) (Q t.succ)

/-- The finite source witnesses in Equation (10); these are computed, not inputs. -/
def densityFactor (N : ℕ) : ℕ := (N + 1) * 2 ^ N

noncomputable def columnCount (n : ℕ) : ℕ :=
  let N := 20 * n
  let k := attackHorizon n N
  2 * N ^ n * (100 * k * N * 2 ^ N * densityFactor N ^ k) ^ 2

end IsRandomnessNecessaryADA.Plain


