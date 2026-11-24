-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunks
-- name    : CSL_Circuit_MemoryAccess_PhysicalFrameEventChunks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:41:27.377673+00:00
-- url     : https://prove2.me/theorems/8631d06a-4073-48cb-98e3-0f32cebfe613
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFrameEventChunks
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventChunks` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventChunks

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_FiniteCircuit_GateSegments

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- List algebra is checked on symbolic chunks, so proof elaboration never
normalizes the 5583 concrete gates or their frame-event annotations. -/
private theorem symbolic_forward_chunks {α β : Type} (ordinary scatter : α → β)
    (copies : List β)
    (x000 x001 x002 x003 x004 x005 x006 x007 x008 x009 x010 x011 x012 x013 x014 x015 x016 x017 x018 x019 x020 x021 x022 x023 x024 x025 x026 x027 x028 x029 x030 x031 x032 x033 x034 x035 x036 x037 x038 x039 x040 x041 x042 x043 x044 x045 x046 x047 x048 x049 x050 x051 x052 x053 x054 x055 x056 x057 x058 x059 x060 x061 x062 x063 x064 x065 x066 x067 x068 x069 x070 x071 x072 x073 x074 x075 x076 x077 x078 x079 x080 x081 x082 x083 x084 x085 x086 x087 x088 x089 x090 x091 x092 x093 x094 x095 x096 x097 x098 x099 x100 x101 x102 x103 x104 x105 x106 x107 x108 x109 x110 x111 x112 x113 x114 x115 x116 x117 x118 x119 x120 x121 x122 x123 x124 x125 x126 x127 x128 x129 x130 x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151 x152 x153 x154 x155 x156 x157 x158 x159 x160 x161 x162 x163 x164 x165 x166 x167 x168 x169 x170 x171 x172 x173 x174 x175 x176 : List α) :
    (x000 ++ x001 ++ x002 ++ x003 ++ x004 ++ x005 ++ x006 ++ x007 ++ x008 ++ x009 ++ x010 ++ x011 ++ x012 ++ x013 ++ x014 ++ x015 ++ x016 ++ x017 ++ x018 ++ x019 ++ x020 ++ x021 ++ x022 ++ x023 ++ x024 ++ x025 ++ x026 ++ x027 ++ x028 ++ x029 ++ x030 ++ x031 ++ x032 ++ x033 ++ x034 ++ x035 ++ x036 ++ x037 ++ x038 ++ x039 ++ x040 ++ x041 ++ x042 ++ x043 ++ x044 ++ x045 ++ x046 ++ x047 ++ x048 ++ x049 ++ x050 ++ x051 ++ x052 ++ x053 ++ x054 ++ x055 ++ x056 ++ x057 ++ x058 ++ x059 ++ x060 ++ x061 ++ x062 ++ x063 ++ x064 ++ x065 ++ x066 ++ x067 ++ x068).map ordinary ++ copies ++
    (x069 ++ x070 ++ x071 ++ x072).map scatter ++
    (x073 ++ x074 ++ x075 ++ x076 ++ x077 ++ x078 ++ x079 ++ x080 ++ x081 ++ x082 ++ x083 ++ x084 ++ x085 ++ x086 ++ x087 ++ x088 ++ x089 ++ x090 ++ x091 ++ x092 ++ x093 ++ x094 ++ x095 ++ x096 ++ x097 ++ x098 ++ x099 ++ x100 ++ x101 ++ x102 ++ x103 ++ x104 ++ x105 ++ x106 ++ x107 ++ x108 ++ x109 ++ x110 ++ x111 ++ x112 ++ x113 ++ x114 ++ x115 ++ x116 ++ x117 ++ x118 ++ x119 ++ x120 ++ x121 ++ x122 ++ x123 ++ x124 ++ x125 ++ x126 ++ x127 ++ x128 ++ x129 ++ x130 ++ x131 ++ x132 ++ x133 ++ x134 ++ x135 ++ x136 ++ x137 ++ x138 ++ x139 ++ x140 ++ x141 ++ x142 ++ x143 ++ x144 ++ x145 ++ x146 ++ x147 ++ x148 ++ x149 ++ x150 ++ x151 ++ x152 ++ x153 ++ x154 ++ x155 ++ x156 ++ x157 ++ x158 ++ x159 ++ x160 ++ x161 ++ x162 ++ x163 ++ x164 ++ x165 ++ x166 ++ x167 ++ x168 ++ x169 ++ x170 ++ x171 ++ x172 ++ x173 ++ x174 ++ x175 ++ x176).map ordinary =
    [(x000.map ordinary), (x001.map ordinary), (x002.map ordinary), (x003.map ordinary), (x004.map ordinary), (x005.map ordinary), (x006.map ordinary), (x007.map ordinary), (x008.map ordinary), (x009.map ordinary), (x010.map ordinary), (x011.map ordinary), (x012.map ordinary), (x013.map ordinary), (x014.map ordinary), (x015.map ordinary), (x016.map ordinary), (x017.map ordinary), (x018.map ordinary), (x019.map ordinary), (x020.map ordinary), (x021.map ordinary), (x022.map ordinary), (x023.map ordinary), (x024.map ordinary), (x025.map ordinary), (x026.map ordinary), (x027.map ordinary), (x028.map ordinary), (x029.map ordinary), (x030.map ordinary), (x031.map ordinary), (x032.map ordinary), (x033.map ordinary), (x034.map ordinary), (x035.map ordinary), (x036.map ordinary), (x037.map ordinary), (x038.map ordinary), (x039.map ordinary), (x040.map ordinary), (x041.map ordinary), (x042.map ordinary), (x043.map ordinary), (x044.map ordinary), (x045.map ordinary), (x046.map ordinary), (x047.map ordinary), (x048.map ordinary), (x049.map ordinary), (x050.map ordinary), (x051.map ordinary), (x052.map ordinary), (x053.map ordinary), (x054.map ordinary), (x055.map ordinary), (x056.map ordinary), (x057.map ordinary), (x058.map ordinary), (x059.map ordinary), (x060.map ordinary), (x061.map ordinary), (x062.map ordinary), (x063.map ordinary), (x064.map ordinary), (x065.map ordinary), (x066.map ordinary), (x067.map ordinary), (x068.map ordinary), copies, (x069.map scatter), (x070.map scatter), (x071.map scatter), (x072.map scatter), (x073.map ordinary), (x074.map ordinary), (x075.map ordinary), (x076.map ordinary), (x077.map ordinary), (x078.map ordinary), (x079.map ordinary), (x080.map ordinary), (x081.map ordinary), (x082.map ordinary), (x083.map ordinary), (x084.map ordinary), (x085.map ordinary), (x086.map ordinary), (x087.map ordinary), (x088.map ordinary), (x089.map ordinary), (x090.map ordinary), (x091.map ordinary), (x092.map ordinary), (x093.map ordinary), (x094.map ordinary), (x095.map ordinary), (x096.map ordinary), (x097.map ordinary), (x098.map ordinary), (x099.map ordinary), (x100.map ordinary), (x101.map ordinary), (x102.map ordinary), (x103.map ordinary), (x104.map ordinary), (x105.map ordinary), (x106.map ordinary), (x107.map ordinary), (x108.map ordinary), (x109.map ordinary), (x110.map ordinary), (x111.map ordinary), (x112.map ordinary), (x113.map ordinary), (x114.map ordinary), (x115.map ordinary), (x116.map ordinary), (x117.map ordinary), (x118.map ordinary), (x119.map ordinary), (x120.map ordinary), (x121.map ordinary), (x122.map ordinary), (x123.map ordinary), (x124.map ordinary), (x125.map ordinary), (x126.map ordinary), (x127.map ordinary), (x128.map ordinary), (x129.map ordinary), (x130.map ordinary), (x131.map ordinary), (x132.map ordinary), (x133.map ordinary), (x134.map ordinary), (x135.map ordinary), (x136.map ordinary), (x137.map ordinary), (x138.map ordinary), (x139.map ordinary), (x140.map ordinary), (x141.map ordinary), (x142.map ordinary), (x143.map ordinary), (x144.map ordinary), (x145.map ordinary), (x146.map ordinary), (x147.map ordinary), (x148.map ordinary), (x149.map ordinary), (x150.map ordinary), (x151.map ordinary), (x152.map ordinary), (x153.map ordinary), (x154.map ordinary), (x155.map ordinary), (x156.map ordinary), (x157.map ordinary), (x158.map ordinary), (x159.map ordinary), (x160.map ordinary), (x161.map ordinary), (x162.map ordinary), (x163.map ordinary), (x164.map ordinary), (x165.map ordinary), (x166.map ordinary), (x167.map ordinary), (x168.map ordinary), (x169.map ordinary), (x170.map ordinary), (x171.map ordinary), (x172.map ordinary), (x173.map ordinary), (x174.map ordinary), (x175.map ordinary), (x176.map ordinary)].flatten := by
  simp only [List.map_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem forwardEvents_chunks : forwardEvents = forwardEventChunks.flatten := by
  have hp : physicalPrefix = prefixChunks := prefix_by_chunks
  have hc : physicalScatter = scatterChunks := scatter_by_chunks
  have hs : physicalSuffix = suffixChunks := suffix_by_chunks
  calc
    forwardEvents = prefixChunks.map ordinaryEvent ++ (List.range 9).map copyEvent ++
        scatterChunks.map scatterEvent ++ suffixChunks.map ordinaryEvent := by
      unfold forwardEvents
      rw [hp, hc, hs]
    _ = forwardEventChunks.flatten :=
      symbolic_forward_chunks ordinaryEvent scatterEvent ((List.range 9).map copyEvent)
        gatesChunk0.toList
        gatesChunk1.toList
        gatesChunk2.toList
        gatesChunk3.toList
        gatesChunk4.toList
        gatesChunk5.toList
        gatesChunk6.toList
        gatesChunk7.toList
        gatesChunk8.toList
        gatesChunk9.toList
        gatesChunk10.toList
        gatesChunk11.toList
        gatesChunk12.toList
        gatesChunk13.toList
        gatesChunk14.toList
        gatesChunk15.toList
        gatesChunk16.toList
        gatesChunk17.toList
        gatesChunk18.toList
        gatesChunk19.toList
        gatesChunk20.toList
        gatesChunk21.toList
        gatesChunk22.toList
        gatesChunk23.toList
        gatesChunk24.toList
        gatesChunk25.toList
        gatesChunk26.toList
        gatesChunk27.toList
        gatesChunk28.toList
        gatesChunk29.toList
        gatesChunk30.toList
        gatesChunk31.toList
        gatesChunk32.toList
        gatesChunk33.toList
        gatesChunk34.toList
        gatesChunk35.toList
        gatesChunk36.toList
        gatesChunk37.toList
        gatesChunk38.toList
        gatesChunk39.toList
        gatesChunk40.toList
        gatesChunk41.toList
        gatesChunk42.toList
        gatesChunk43.toList
        gatesChunk44.toList
        gatesChunk45.toList
        gatesChunk46.toList
        gatesChunk47.toList
        gatesChunk48.toList
        gatesChunk49.toList
        gatesChunk50.toList
        gatesChunk51.toList
        gatesChunk52.toList
        gatesChunk53.toList
        gatesChunk54.toList
        gatesChunk55.toList
        gatesChunk56.toList
        gatesChunk57.toList
        gatesChunk58.toList
        gatesChunk59.toList
        gatesChunk60.toList
        gatesChunk61.toList
        gatesChunk62.toList
        gatesChunk63.toList
        gatesChunk64.toList
        gatesChunk65.toList
        gatesChunk66.toList
        gatesChunk67.toList
        (gatesChunk68.toList.take 10)
        (gatesChunk68.toList.drop 10)
        gatesChunk69.toList
        gatesChunk70.toList
        (gatesChunk71.toList.take 25)
        (gatesChunk71.toList.drop 25)
        gatesChunk72.toList
        gatesChunk73.toList
        gatesChunk74.toList
        gatesChunk75.toList
        gatesChunk76.toList
        gatesChunk77.toList
        gatesChunk78.toList
        gatesChunk79.toList
        gatesChunk80.toList
        gatesChunk81.toList
        gatesChunk82.toList
        gatesChunk83.toList
        gatesChunk84.toList
        gatesChunk85.toList
        gatesChunk86.toList
        gatesChunk87.toList
        gatesChunk88.toList
        gatesChunk89.toList
        gatesChunk90.toList
        gatesChunk91.toList
        gatesChunk92.toList
        gatesChunk93.toList
        gatesChunk94.toList
        gatesChunk95.toList
        gatesChunk96.toList
        gatesChunk97.toList
        gatesChunk98.toList
        gatesChunk99.toList
        gatesChunk100.toList
        gatesChunk101.toList
        gatesChunk102.toList
        gatesChunk103.toList
        gatesChunk104.toList
        gatesChunk105.toList
        gatesChunk106.toList
        gatesChunk107.toList
        gatesChunk108.toList
        gatesChunk109.toList
        gatesChunk110.toList
        gatesChunk111.toList
        gatesChunk112.toList
        gatesChunk113.toList
        gatesChunk114.toList
        gatesChunk115.toList
        gatesChunk116.toList
        gatesChunk117.toList
        gatesChunk118.toList
        gatesChunk119.toList
        gatesChunk120.toList
        gatesChunk121.toList
        gatesChunk122.toList
        gatesChunk123.toList
        gatesChunk124.toList
        gatesChunk125.toList
        gatesChunk126.toList
        gatesChunk127.toList
        gatesChunk128.toList
        gatesChunk129.toList
        gatesChunk130.toList
        gatesChunk131.toList
        gatesChunk132.toList
        gatesChunk133.toList
        gatesChunk134.toList
        gatesChunk135.toList
        gatesChunk136.toList
        gatesChunk137.toList
        gatesChunk138.toList
        gatesChunk139.toList
        gatesChunk140.toList
        gatesChunk141.toList
        gatesChunk142.toList
        gatesChunk143.toList
        gatesChunk144.toList
        gatesChunk145.toList
        gatesChunk146.toList
        gatesChunk147.toList
        gatesChunk148.toList
        gatesChunk149.toList
        gatesChunk150.toList
        gatesChunk151.toList
        gatesChunk152.toList
        gatesChunk153.toList
        gatesChunk154.toList
        gatesChunk155.toList
        gatesChunk156.toList
        gatesChunk157.toList
        gatesChunk158.toList
        gatesChunk159.toList
        gatesChunk160.toList
        gatesChunk161.toList
        gatesChunk162.toList
        gatesChunk163.toList
        gatesChunk164.toList
        gatesChunk165.toList
        gatesChunk166.toList
        gatesChunk167.toList
        gatesChunk168.toList
        gatesChunk169.toList
        gatesChunk170.toList
        gatesChunk171.toList
        gatesChunk172.toList
        gatesChunk173.toList
        gatesChunk174.toList

theorem eventVisits_flatten (r : Nat) (chunks : List (List FrameEvent)) :
    eventVisits r chunks.flatten = (chunks.map (eventVisits r)).flatten := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatten_cons, List.map_cons, eventVisits_append, ih]

private theorem symbolic_visits_chunks (visit : List FrameEvent → List Nat)
    (c000 c001 c002 c003 c004 c005 c006 c007 c008 c009 c010 c011 c012 c013 c014 c015 c016 c017 c018 c019 c020 c021 c022 c023 c024 c025 c026 c027 c028 c029 c030 c031 c032 c033 c034 c035 c036 c037 c038 c039 c040 c041 c042 c043 c044 c045 c046 c047 c048 c049 c050 c051 c052 c053 c054 c055 c056 c057 c058 c059 c060 c061 c062 c063 c064 c065 c066 c067 c068 c069 c070 c071 c072 c073 c074 c075 c076 c077 c078 c079 c080 c081 c082 c083 c084 c085 c086 c087 c088 c089 c090 c091 c092 c093 c094 c095 c096 c097 c098 c099 c100 c101 c102 c103 c104 c105 c106 c107 c108 c109 c110 c111 c112 c113 c114 c115 c116 c117 c118 c119 c120 c121 c122 c123 c124 c125 c126 c127 c128 c129 c130 c131 c132 c133 c134 c135 c136 c137 c138 c139 c140 c141 c142 c143 c144 c145 c146 c147 c148 c149 c150 c151 c152 c153 c154 c155 c156 c157 c158 c159 c160 c161 c162 c163 c164 c165 c166 c167 c168 c169 c170 c171 c172 c173 c174 c175 c176 c177 : List FrameEvent) :
    ([c000, c001, c002, c003, c004, c005, c006, c007, c008, c009, c010, c011, c012, c013, c014, c015, c016, c017, c018, c019, c020, c021, c022, c023, c024, c025, c026, c027, c028, c029, c030, c031, c032, c033, c034, c035, c036, c037, c038, c039, c040, c041, c042, c043, c044, c045, c046, c047, c048, c049, c050, c051, c052, c053, c054, c055, c056, c057, c058, c059, c060, c061, c062, c063, c064, c065, c066, c067, c068, c069, c070, c071, c072, c073, c074, c075, c076, c077, c078, c079, c080, c081, c082, c083, c084, c085, c086, c087, c088, c089, c090, c091, c092, c093, c094, c095, c096, c097, c098, c099, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143, c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159, c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175, c176, c177].map visit).flatten =
    visit c000 ++ visit c001 ++ visit c002 ++ visit c003 ++ visit c004 ++ visit c005 ++ visit c006 ++ visit c007 ++ visit c008 ++ visit c009 ++ visit c010 ++ visit c011 ++ visit c012 ++ visit c013 ++ visit c014 ++ visit c015 ++ visit c016 ++ visit c017 ++ visit c018 ++ visit c019 ++ visit c020 ++ visit c021 ++ visit c022 ++ visit c023 ++ visit c024 ++ visit c025 ++ visit c026 ++ visit c027 ++ visit c028 ++ visit c029 ++ visit c030 ++ visit c031 ++ visit c032 ++ visit c033 ++ visit c034 ++ visit c035 ++ visit c036 ++ visit c037 ++ visit c038 ++ visit c039 ++ visit c040 ++ visit c041 ++ visit c042 ++ visit c043 ++ visit c044 ++ visit c045 ++ visit c046 ++ visit c047 ++ visit c048 ++ visit c049 ++ visit c050 ++ visit c051 ++ visit c052 ++ visit c053 ++ visit c054 ++ visit c055 ++ visit c056 ++ visit c057 ++ visit c058 ++ visit c059 ++ visit c060 ++ visit c061 ++ visit c062 ++ visit c063 ++ visit c064 ++ visit c065 ++ visit c066 ++ visit c067 ++ visit c068 ++ visit c069 ++ visit c070 ++ visit c071 ++ visit c072 ++ visit c073 ++ visit c074 ++ visit c075 ++ visit c076 ++ visit c077 ++ visit c078 ++ visit c079 ++ visit c080 ++ visit c081 ++ visit c082 ++ visit c083 ++ visit c084 ++ visit c085 ++ visit c086 ++ visit c087 ++ visit c088 ++ visit c089 ++ visit c090 ++ visit c091 ++ visit c092 ++ visit c093 ++ visit c094 ++ visit c095 ++ visit c096 ++ visit c097 ++ visit c098 ++ visit c099 ++ visit c100 ++ visit c101 ++ visit c102 ++ visit c103 ++ visit c104 ++ visit c105 ++ visit c106 ++ visit c107 ++ visit c108 ++ visit c109 ++ visit c110 ++ visit c111 ++ visit c112 ++ visit c113 ++ visit c114 ++ visit c115 ++ visit c116 ++ visit c117 ++ visit c118 ++ visit c119 ++ visit c120 ++ visit c121 ++ visit c122 ++ visit c123 ++ visit c124 ++ visit c125 ++ visit c126 ++ visit c127 ++ visit c128 ++ visit c129 ++ visit c130 ++ visit c131 ++ visit c132 ++ visit c133 ++ visit c134 ++ visit c135 ++ visit c136 ++ visit c137 ++ visit c138 ++ visit c139 ++ visit c140 ++ visit c141 ++ visit c142 ++ visit c143 ++ visit c144 ++ visit c145 ++ visit c146 ++ visit c147 ++ visit c148 ++ visit c149 ++ visit c150 ++ visit c151 ++ visit c152 ++ visit c153 ++ visit c154 ++ visit c155 ++ visit c156 ++ visit c157 ++ visit c158 ++ visit c159 ++ visit c160 ++ visit c161 ++ visit c162 ++ visit c163 ++ visit c164 ++ visit c165 ++ visit c166 ++ visit c167 ++ visit c168 ++ visit c169 ++ visit c170 ++ visit c171 ++ visit c172 ++ visit c173 ++ visit c174 ++ visit c175 ++ visit c176 ++ visit c177 := by
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem forward_visits_chunks (r : Nat) : eventVisits r forwardEvents =
      eventVisits r forwardEventChunk000 ++
      eventVisits r forwardEventChunk001 ++
      eventVisits r forwardEventChunk002 ++
      eventVisits r forwardEventChunk003 ++
      eventVisits r forwardEventChunk004 ++
      eventVisits r forwardEventChunk005 ++
      eventVisits r forwardEventChunk006 ++
      eventVisits r forwardEventChunk007 ++
      eventVisits r forwardEventChunk008 ++
      eventVisits r forwardEventChunk009 ++
      eventVisits r forwardEventChunk010 ++
      eventVisits r forwardEventChunk011 ++
      eventVisits r forwardEventChunk012 ++
      eventVisits r forwardEventChunk013 ++
      eventVisits r forwardEventChunk014 ++
      eventVisits r forwardEventChunk015 ++
      eventVisits r forwardEventChunk016 ++
      eventVisits r forwardEventChunk017 ++
      eventVisits r forwardEventChunk018 ++
      eventVisits r forwardEventChunk019 ++
      eventVisits r forwardEventChunk020 ++
      eventVisits r forwardEventChunk021 ++
      eventVisits r forwardEventChunk022 ++
      eventVisits r forwardEventChunk023 ++
      eventVisits r forwardEventChunk024 ++
      eventVisits r forwardEventChunk025 ++
      eventVisits r forwardEventChunk026 ++
      eventVisits r forwardEventChunk027 ++
      eventVisits r forwardEventChunk028 ++
      eventVisits r forwardEventChunk029 ++
      eventVisits r forwardEventChunk030 ++
      eventVisits r forwardEventChunk031 ++
      eventVisits r forwardEventChunk032 ++
      eventVisits r forwardEventChunk033 ++
      eventVisits r forwardEventChunk034 ++
      eventVisits r forwardEventChunk035 ++
      eventVisits r forwardEventChunk036 ++
      eventVisits r forwardEventChunk037 ++
      eventVisits r forwardEventChunk038 ++
      eventVisits r forwardEventChunk039 ++
      eventVisits r forwardEventChunk040 ++
      eventVisits r forwardEventChunk041 ++
      eventVisits r forwardEventChunk042 ++
      eventVisits r forwardEventChunk043 ++
      eventVisits r forwardEventChunk044 ++
      eventVisits r forwardEventChunk045 ++
      eventVisits r forwardEventChunk046 ++
      eventVisits r forwardEventChunk047 ++
      eventVisits r forwardEventChunk048 ++
      eventVisits r forwardEventChunk049 ++
      eventVisits r forwardEventChunk050 ++
      eventVisits r forwardEventChunk051 ++
      eventVisits r forwardEventChunk052 ++
      eventVisits r forwardEventChunk053 ++
      eventVisits r forwardEventChunk054 ++
      eventVisits r forwardEventChunk055 ++
      eventVisits r forwardEventChunk056 ++
      eventVisits r forwardEventChunk057 ++
      eventVisits r forwardEventChunk058 ++
      eventVisits r forwardEventChunk059 ++
      eventVisits r forwardEventChunk060 ++
      eventVisits r forwardEventChunk061 ++
      eventVisits r forwardEventChunk062 ++
      eventVisits r forwardEventChunk063 ++
      eventVisits r forwardEventChunk064 ++
      eventVisits r forwardEventChunk065 ++
      eventVisits r forwardEventChunk066 ++
      eventVisits r forwardEventChunk067 ++
      eventVisits r forwardEventChunk068 ++
      eventVisits r forwardEventChunk069 ++
      eventVisits r forwardEventChunk070 ++
      eventVisits r forwardEventChunk071 ++
      eventVisits r forwardEventChunk072 ++
      eventVisits r forwardEventChunk073 ++
      eventVisits r forwardEventChunk074 ++
      eventVisits r forwardEventChunk075 ++
      eventVisits r forwardEventChunk076 ++
      eventVisits r forwardEventChunk077 ++
      eventVisits r forwardEventChunk078 ++
      eventVisits r forwardEventChunk079 ++
      eventVisits r forwardEventChunk080 ++
      eventVisits r forwardEventChunk081 ++
      eventVisits r forwardEventChunk082 ++
      eventVisits r forwardEventChunk083 ++
      eventVisits r forwardEventChunk084 ++
      eventVisits r forwardEventChunk085 ++
      eventVisits r forwardEventChunk086 ++
      eventVisits r forwardEventChunk087 ++
      eventVisits r forwardEventChunk088 ++
      eventVisits r forwardEventChunk089 ++
      eventVisits r forwardEventChunk090 ++
      eventVisits r forwardEventChunk091 ++
      eventVisits r forwardEventChunk092 ++
      eventVisits r forwardEventChunk093 ++
      eventVisits r forwardEventChunk094 ++
      eventVisits r forwardEventChunk095 ++
      eventVisits r forwardEventChunk096 ++
      eventVisits r forwardEventChunk097 ++
      eventVisits r forwardEventChunk098 ++
      eventVisits r forwardEventChunk099 ++
      eventVisits r forwardEventChunk100 ++
      eventVisits r forwardEventChunk101 ++
      eventVisits r forwardEventChunk102 ++
      eventVisits r forwardEventChunk103 ++
      eventVisits r forwardEventChunk104 ++
      eventVisits r forwardEventChunk105 ++
      eventVisits r forwardEventChunk106 ++
      eventVisits r forwardEventChunk107 ++
      eventVisits r forwardEventChunk108 ++
      eventVisits r forwardEventChunk109 ++
      eventVisits r forwardEventChunk110 ++
      eventVisits r forwardEventChunk111 ++
      eventVisits r forwardEventChunk112 ++
      eventVisits r forwardEventChunk113 ++
      eventVisits r forwardEventChunk114 ++
      eventVisits r forwardEventChunk115 ++
      eventVisits r forwardEventChunk116 ++
      eventVisits r forwardEventChunk117 ++
      eventVisits r forwardEventChunk118 ++
      eventVisits r forwardEventChunk119 ++
      eventVisits r forwardEventChunk120 ++
      eventVisits r forwardEventChunk121 ++
      eventVisits r forwardEventChunk122 ++
      eventVisits r forwardEventChunk123 ++
      eventVisits r forwardEventChunk124 ++
      eventVisits r forwardEventChunk125 ++
      eventVisits r forwardEventChunk126 ++
      eventVisits r forwardEventChunk127 ++
      eventVisits r forwardEventChunk128 ++
      eventVisits r forwardEventChunk129 ++
      eventVisits r forwardEventChunk130 ++
      eventVisits r forwardEventChunk131 ++
      eventVisits r forwardEventChunk132 ++
      eventVisits r forwardEventChunk133 ++
      eventVisits r forwardEventChunk134 ++
      eventVisits r forwardEventChunk135 ++
      eventVisits r forwardEventChunk136 ++
      eventVisits r forwardEventChunk137 ++
      eventVisits r forwardEventChunk138 ++
      eventVisits r forwardEventChunk139 ++
      eventVisits r forwardEventChunk140 ++
      eventVisits r forwardEventChunk141 ++
      eventVisits r forwardEventChunk142 ++
      eventVisits r forwardEventChunk143 ++
      eventVisits r forwardEventChunk144 ++
      eventVisits r forwardEventChunk145 ++
      eventVisits r forwardEventChunk146 ++
      eventVisits r forwardEventChunk147 ++
      eventVisits r forwardEventChunk148 ++
      eventVisits r forwardEventChunk149 ++
      eventVisits r forwardEventChunk150 ++
      eventVisits r forwardEventChunk151 ++
      eventVisits r forwardEventChunk152 ++
      eventVisits r forwardEventChunk153 ++
      eventVisits r forwardEventChunk154 ++
      eventVisits r forwardEventChunk155 ++
      eventVisits r forwardEventChunk156 ++
      eventVisits r forwardEventChunk157 ++
      eventVisits r forwardEventChunk158 ++
      eventVisits r forwardEventChunk159 ++
      eventVisits r forwardEventChunk160 ++
      eventVisits r forwardEventChunk161 ++
      eventVisits r forwardEventChunk162 ++
      eventVisits r forwardEventChunk163 ++
      eventVisits r forwardEventChunk164 ++
      eventVisits r forwardEventChunk165 ++
      eventVisits r forwardEventChunk166 ++
      eventVisits r forwardEventChunk167 ++
      eventVisits r forwardEventChunk168 ++
      eventVisits r forwardEventChunk169 ++
      eventVisits r forwardEventChunk170 ++
      eventVisits r forwardEventChunk171 ++
      eventVisits r forwardEventChunk172 ++
      eventVisits r forwardEventChunk173 ++
      eventVisits r forwardEventChunk174 ++
      eventVisits r forwardEventChunk175 ++
      eventVisits r forwardEventChunk176 ++
      eventVisits r forwardEventChunk177 := by
  calc
    eventVisits r forwardEvents =
        (forwardEventChunks.map (eventVisits r)).flatten :=
      (congrArg (eventVisits r) forwardEvents_chunks).trans
        (eventVisits_flatten r forwardEventChunks)
    _ = _ := symbolic_visits_chunks (eventVisits r)
      forwardEventChunk000
      forwardEventChunk001
      forwardEventChunk002
      forwardEventChunk003
      forwardEventChunk004
      forwardEventChunk005
      forwardEventChunk006
      forwardEventChunk007
      forwardEventChunk008
      forwardEventChunk009
      forwardEventChunk010
      forwardEventChunk011
      forwardEventChunk012
      forwardEventChunk013
      forwardEventChunk014
      forwardEventChunk015
      forwardEventChunk016
      forwardEventChunk017
      forwardEventChunk018
      forwardEventChunk019
      forwardEventChunk020
      forwardEventChunk021
      forwardEventChunk022
      forwardEventChunk023
      forwardEventChunk024
      forwardEventChunk025
      forwardEventChunk026
      forwardEventChunk027
      forwardEventChunk028
      forwardEventChunk029
      forwardEventChunk030
      forwardEventChunk031
      forwardEventChunk032
      forwardEventChunk033
      forwardEventChunk034
      forwardEventChunk035
      forwardEventChunk036
      forwardEventChunk037
      forwardEventChunk038
      forwardEventChunk039
      forwardEventChunk040
      forwardEventChunk041
      forwardEventChunk042
      forwardEventChunk043
      forwardEventChunk044
      forwardEventChunk045
      forwardEventChunk046
      forwardEventChunk047
      forwardEventChunk048
      forwardEventChunk049
      forwardEventChunk050
      forwardEventChunk051
      forwardEventChunk052
      forwardEventChunk053
      forwardEventChunk054
      forwardEventChunk055
      forwardEventChunk056
      forwardEventChunk057
      forwardEventChunk058
      forwardEventChunk059
      forwardEventChunk060
      forwardEventChunk061
      forwardEventChunk062
      forwardEventChunk063
      forwardEventChunk064
      forwardEventChunk065
      forwardEventChunk066
      forwardEventChunk067
      forwardEventChunk068
      forwardEventChunk069
      forwardEventChunk070
      forwardEventChunk071
      forwardEventChunk072
      forwardEventChunk073
      forwardEventChunk074
      forwardEventChunk075
      forwardEventChunk076
      forwardEventChunk077
      forwardEventChunk078
      forwardEventChunk079
      forwardEventChunk080
      forwardEventChunk081
      forwardEventChunk082
      forwardEventChunk083
      forwardEventChunk084
      forwardEventChunk085
      forwardEventChunk086
      forwardEventChunk087
      forwardEventChunk088
      forwardEventChunk089
      forwardEventChunk090
      forwardEventChunk091
      forwardEventChunk092
      forwardEventChunk093
      forwardEventChunk094
      forwardEventChunk095
      forwardEventChunk096
      forwardEventChunk097
      forwardEventChunk098
      forwardEventChunk099
      forwardEventChunk100
      forwardEventChunk101
      forwardEventChunk102
      forwardEventChunk103
      forwardEventChunk104
      forwardEventChunk105
      forwardEventChunk106
      forwardEventChunk107
      forwardEventChunk108
      forwardEventChunk109
      forwardEventChunk110
      forwardEventChunk111
      forwardEventChunk112
      forwardEventChunk113
      forwardEventChunk114
      forwardEventChunk115
      forwardEventChunk116
      forwardEventChunk117
      forwardEventChunk118
      forwardEventChunk119
      forwardEventChunk120
      forwardEventChunk121
      forwardEventChunk122
      forwardEventChunk123
      forwardEventChunk124
      forwardEventChunk125
      forwardEventChunk126
      forwardEventChunk127
      forwardEventChunk128
      forwardEventChunk129
      forwardEventChunk130
      forwardEventChunk131
      forwardEventChunk132
      forwardEventChunk133
      forwardEventChunk134
      forwardEventChunk135
      forwardEventChunk136
      forwardEventChunk137
      forwardEventChunk138
      forwardEventChunk139
      forwardEventChunk140
      forwardEventChunk141
      forwardEventChunk142
      forwardEventChunk143
      forwardEventChunk144
      forwardEventChunk145
      forwardEventChunk146
      forwardEventChunk147
      forwardEventChunk148
      forwardEventChunk149
      forwardEventChunk150
      forwardEventChunk151
      forwardEventChunk152
      forwardEventChunk153
      forwardEventChunk154
      forwardEventChunk155
      forwardEventChunk156
      forwardEventChunk157
      forwardEventChunk158
      forwardEventChunk159
      forwardEventChunk160
      forwardEventChunk161
      forwardEventChunk162
      forwardEventChunk163
      forwardEventChunk164
      forwardEventChunk165
      forwardEventChunk166
      forwardEventChunk167
      forwardEventChunk168
      forwardEventChunk169
      forwardEventChunk170
      forwardEventChunk171
      forwardEventChunk172
      forwardEventChunk173
      forwardEventChunk174
      forwardEventChunk175
      forwardEventChunk176
      forwardEventChunk177

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.forwardEvents_chunks
#print axioms CSL.Construction.PhysicalFramePaths.forward_visits_chunks


